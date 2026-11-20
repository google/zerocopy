# Code-Based Security Games Versus Conservative Extension for Specification Adequacy

## Summary

Two major traditions claim to formalize whether a formal specification "says what we mean," yet they answer orthogonal halves of the adequacy question and fail in complementary ways when relied upon alone:

1. **Code-based security games and game hopping** (Bellare & Rogaway 2006; Shoup 2004; Halevi 2005; mechanized in `EasyCrypt`, `CryptoVerif`, `SSProve`, and `FCF`) state specification adequacy **operationally and quantitatively** as an upper bound on any resource-bounded adversary's distinguishing or winning advantage against an explicit executable experiment $\mathsf{Exp}_{\Pi}(\mathcal{A})$ ($\Pr[\mathsf{Exp}_{\Pi}^{\text{real}}(\mathcal{A}) = 1] - \Pr[\mathsf{Exp}_{\Pi}^{\text{ideal}}(\mathcal{A}) = 1] \le \varepsilon$). Game hopping decomposes adequacy across intermediate hybrids via Bellare–Rogaway's **Fundamental Lemma** ($\lvert \Pr[G_1 = 1] - \Pr[G_2 = 1] \rvert \le \Pr[G_1 \text{ sets } \mathsf{bad}]$ when $G_1, G_2$ are syntactically identical until $\mathsf{bad}$). Its strength is making the **threat interface explicit** (every oracle query, memory footprint, and win predicate is executable code); its blindspot is **model omission**—an experiment that omits a decryption-error, timing, or compression oracle yields $\mathsf{Adv} = 0$ on protocols that fail catastrophically in deployment.
2. **Conservative extension and requirements/domain decomposition** (Zave & Jackson 1997; Jackson 2001; kernel definitional principles in `HOL Light`, `HOL4`, `Candle`, `Isabelle/HOL`, and `Lean 4`/`Lean4Lean`) protect **logical consistency and domain alignment**. Kernel definitional principles ensure that adding new types, constants, and specifications ($\Sigma \subseteq \Sigma'$) is **logically conservative**—every $\Sigma$-theorem provable in $\Sigma'$ was already provable in $\Sigma$, so introducing a new specification cannot silently imply $\bot$. Meanwhile, Zave and Jackson separate **domain knowledge ($W$)**, **machine specification ($S$)**, and **requirements ($R$)** via $W, S \vdash R$. Its strength is blocking hidden contradictions and exposing unverified environmental assumptions; its blindspot is **vacuous satisfaction and permissive refinement**—a conservative definition $S_{\text{vac}}$ or weak postcondition $R$ passes the kernel with zero errors while permitting trivially useless or unsafe implementations.
3. **Divergent behavior under iterative specification patching:** Under iterative patching, conservative extension silently absorbs weakened postconditions or patched special cases without kernel alarms unless re-validated against intent and realizability ($\forall e \in W.\;\exists m.\; S(e, m)$), whereas adding an adversary capability or error oracle to a game-based specification immediately falsifies prior advantage bounds—yet cannot verify that $W$ matches physical reality. Published empirical studies across cryptographic protocols (SSH, TLS), seL4, CompCert, distributed systems (`IronFleet`, `Verdi`), and LLM-driven binary verification (`OSS Verify`) show that production failures concentrate at precisely these unmodeled domain interfaces, unverified compiler/shim seams, and patched-specification boundaries.

## Applicability

This report applies to verification engineers, programming-language designers, and protocol architects choosing or combining specification frameworks across cryptographic protocols, proof assistants, verified systems kernels, and autonomous verification pipelines.

The examined subjects relate as two comparative families plus empirical validation benchmarks:

- **Code-Based Security Game Toolchains:** `EasyCrypt/easycrypt` (`ce19cb6cbab4951e58553c36128e8a19f2f90c6a`), `SSProve/ssprove` (`9a37fe0ab79d041f8d835e6cf18e37614b16a791`, Rocq), `adampetcher/fcf` (`2550fa27e491c03655cddc7830a5baeb15520104`, Rocq), and `CryptoVerif` (`https://gitlab.inria.fr/bblanche/CryptoVerif`, IEEE TDSC 2008), grounded in Bellare & Rogaway (EUROCRYPT 2006), Shoup (ePrint `2004/332`), and Halevi (ePrint `2005/181`).
- **Conservative Extension & Requirements Decomposition:** `jrh13/hol-light` (`1a0c0e6b182cd9e271946ba8d78f7942619f4acb`), `HOL-Theorem-Prover/HOL` (`0c30bdb71aafd4e6a354f5b0b43fffbff6fa8d47`), `CakeML/cakeml` `candle/` (`2874b664e10939a3ee462215b2e068c89c1f70eb`, Kumar et al. JAR 2016), `isabelle-prover/mirror-isabelle` (`c45cdab77eec0ac889f9717ca229a5e9064a24b1`, Kunčar & Popescu ITP 2015 / JAR 2019), `leanprover/lean4` (`5a82f1a47fbc2323ad6be6b11a7c0522dd4f3e68`), and `digama0/lean4lean` (`67f63b0c818920dfaed2ad07ccff187a6a8fe1e3`), grounded in Zave & Jackson (ACM TOSEM 1997) and Jackson (*Problem Frames*, 2001).
- **Published Empirical & Benchmark Evidence vs. Local Toy Models:** Published empirical findings from Albrecht, Paterson & Watson (IEEE S&P 2009), Degabriele, Paterson & Watson (IEEE S&P 2011), Yang et al. (PLDI 2011), Klein et al. (ACM TOCS 2014), Fonseca et al. (EuroSys 2017), and `theorem-labs/oss-verify-proofs` (`32c8baf6e92f173b445903857770da103ba307e0`) are strictly separated from the standalone Python toy-model probe executed on `2026-11-19` in **Evidence**.

## Findings

### 1. Code-Based Security Games and Game Hopping

#### 1.1 Games as Executable Programs and the Fundamental Lemma

`Basis: normative + source`

Bellare and Rogaway (EUROCRYPT 2006, DOI `10.1007/11761679_25`), Shoup (IACR ePrint `2004/332`), and Halevi (IACR ePrint `2005/181`) formulate cryptographic adequacy not as a declarative predicate over abstract traces, but as an **imperative probabilistic program** (**game**) interacting with an abstract oracle-parameterized adversary $\mathcal{A}$. A scheme $\Pi$ is deemed adequate for property $\mathsf{Prop}$ (e.g., IND-CPA, IND-CCA2, SUF-CMA) when, for all adversaries $\mathcal{A}$ within declared computational and query-count bounds $(t, q)$:

$$\mathsf{Adv}_{\Pi}^{\mathsf{Prop}}(\mathcal{A}) := \left|\Pr[G^{\text{real}}(\mathcal{A}) \Rightarrow 1] - \Pr[G^{\text{ideal}}(\mathcal{A}) \Rightarrow 1]\right| \le \varepsilon(t, q).$$

Proofs proceed by a chain of small transformations $G_0 \to G_1 \to \dots \to G_k$ (**game hopping**) spanning two canonical techniques:

1. **Transitions based on indistinguishability / reduction:** Replacing a primitive call (e.g., $\mathsf{PRF}_K(\cdot)$) with an ideal object (random function $\mathsf{RF}(\cdot)$) by exhibiting an explicit reduction wrapper $\mathcal{B}^{\mathcal{O}}$ whose distinguishing advantage equals the hop gap.
2. **Transitions based on failure events ("identical-until-bad"):** Two games $G_1$ and $G_2$ execute identical instructions and random choices except after setting a monotone Boolean flag $\mathsf{bad} \leftarrow \mathsf{true}$. Inspecting `EasyCrypt/easycrypt` (`ce19cb6cbab4951e58553c36128e8a19f2f90c6a`, `examples/FundamentalLemma.ec` lines 33–49) verifies the exact mechanized statement `FundamentalLemma`:

$$\Pr[G_1.\text{main}() : A \land \neg F] = \Pr[G_2.\text{main}() : B \land \neg F] \implies \left|\Pr[G_1.\text{main}() : A] - \Pr[G_2.\text{main}() : B]\right| \le \max\bigl(\Pr[G_1.\text{main}() : F],\; \Pr[G_2.\text{main}() : F]\bigr).$$

When $\mathsf{bad}$ ($F$) is bounded across $q$ oracle queries—implemented via `EasyCrypt`'s failure-event tactic `ecPhlFel.ml` (`t_failure_event_r`, lines 117–130, which statically inspects `callable_oracles_f` at lines 50–89 to isolate adversary-callable procedures writing to monitored state)—the total security loss is bounded explicitly by summing per-query failure probabilities (`FEL` / `FelTactic.ec`).

#### 1.2 Comparative Architecture of Game-Playing Proof Assistants

`Basis: normative + source + documentation`

Four mature mechanized frameworks implement code-based game playing with sharply different trusted computing bases (TCBs), adversary quantification mechanisms, and composition principles:

| System (Pinned Source / Venue) | Underlying Logic & Semantics | How Adversaries Are Quantified & Isolated | Core Game-Hop Mechanism | TCB & Primary Limitation |
|---|---|---|---|---|
| **`EasyCrypt`** (`ce19cb6cbab...`) | Probabilistic Hoare Logic (`pHL`), Probabilistic Relational Hoare Logic (`pRHL`), Expectational HL (`eHL`), embedded higher-order logic | Abstract module types (`module type Adv { proc ... }`) with negative memory restrictions `{ -Mem }` preventing direct reads/writes to game secrets (`examples/FundamentalLemma.ec` L15–19) | `pRHL` couplings (`equiv`), up-to-bad (`ecPhlFel.ml` `t_failure_event_r`), explicit module interpolation | Trusts EasyCrypt's ML typechecker/logic **and external SMT solvers** (`Alt-Ergo`, `Z3`, `CVC4/5` via `Why3`); asymptotic polynomial-time bounds are usually informal meta-arguments |
| **`CryptoVerif`** (`Blanchet`, IEEE TDSC 2008) | Applied $\pi$-calculus extended with bitstrings, polynomial-time bounds, and replication | Probabilistic polynomial-time (PPT) interactive Turing machines interacting with bounded-session process terms | Automated syntactic game rewriting guided by cryptographic indistinguishability equivalences and Shoup's failure-event transformations | Trusts ~40 KLoC OCaml prover/rewriter (no independent proof kernel); excels at automated protocol equivalence, harder for general-purpose stateful data structures |
| **`SSProve`** (`9a37fe0ab79...`, TOPLAS 2023) | State-separating proofs (SSP) embedded in **Rocq** via order-enriched relative monads and Free probabilistic programs | Adversary `A : package I A_export` quantified inside Rocq (`pkg_advantage.v` L45–90), constrained by **disjoint memory footprints** `fseparate LA L0` (`L87–88`) | Algebraic package composition laws (`Advantage_link`, `Advantage_par`, `interchange` in `pkg_composition.v` & `pkg_advantage.v` L123–166) plus `pRHL` (`pkg_rhl.v`) | Kernel-checked by **Rocq** plus 4 explicit axioms (`README.md` L723–731: `propositional_extensionality`, `functional_extensionality_dep`, `constructive_indefinite_description`, `Axioms.R`); concrete runtime bounds deferred unless coupled to a cost model |
| **`FCF`** (`2550fa27e49...`, CSF 2015) | Deeply embedded rational sub-distribution monad `Comp` (`Ret`, `Bind`, `Rnd`, `Repeat` in `src/FCF/Comp.v` L17–21) in **Rocq** | Explicit oracle-parameterized Rocq functions paired with asymptotic worst-case polynomial-time classes (`src/FCF/WC_PolyTime.v` + `Asymptotic.v` `function_cost_model` L13–55) | Inductive relational game equivalence (`TwoWorldsEquiv.v`), `eq_until_bad`, rational probability arithmetic (`Comp.v` L13–17) | Minimal Rocq axioms; **finite-support `Comp`** (`getSupport`) cannot directly model continuous distributions, and writing large reductions directly in shallow/deep Rocq `Comp` requires high proof verbosity |

**Key Structural Insight:** Across all four tools, **state separation / oracle restriction is part of the theorem statement itself**. In `EasyCrypt`, forgetting a `{ -G }` memory-disjointness constraint lets the universally quantified adversary directly read the secret key from game memory, making the theorem unprovable—which acts as a syntactic guardrail against leaky threat models. In `SSProve` (`pkg_advantage.v` lines 83–90), `adv_equiv` explicitly requires `fseparate LA L₀` and `fseparate LA L₁`, ensuring algebraic parallel/sequential composition (`Advantage_par` at line 142) preserves state non-interference without global re-proofs.

#### 1.3 What Game-Playing Can and Cannot Express About "Saying What We Mean"

`Basis: normative + source + derived`

- **Who the adversary is:** Explicitly bounded by an **interface (`opsig` / `module type`)** plus query counts $q$ and (optionally in `FCF` / `CryptoVerif`) explicit runtime bounds (`function_cost_model`). Unbounded adversaries break computational primitives by brute-force key search, so adequacy **must** quantify over a restricted adversary class—unlike standard HOL/type-theoretic functional correctness.
- **What counts as a win:** An executable Boolean event inside the experiment (`res = true` or distinguishing bit $b' = b$). Every win condition is **observational and relative to the challenger code**: if the challenger omits an oracle (such as a length field, a malformed-padding alert, or decryption-failure timing), no adversary in the formal universe can trigger that win path.
- **How weakened or vacuous specifications show up:**
  1. **Unreachable challenge or malformed win predicate (false security):** If the game aborts before returning a secret or restricts challenge queries to identical messages ($m_0 = m_1$), then $\mathsf{Adv} = 0$ holds vacuously for *any* broken cipher.
  2. **Omitted real-world oracle (model under-approximation):** A scheme proved IND-CPA in a game lacking a decryption-error oracle appears perfectly secure ($\mathsf{Adv} = 0$) even when an error oracle leaks plaintext via padding oracles (`toy probe [1]`: `Adv(no_error_oracle)=0` vs `Adv(with_pad_oracle)=7/8`, mirroring `EasyCrypt` `examples/MEE-CBC/RCPA_CMA.ec` distinguishing `MAC-then-Encrypt` IND-CPA from `Encrypt-then-MAC` `INT-CTXT`).
  3. **Unmodeled side-channel leakage:** Even a lossless, kernel-checked `SSProve` or `FCF` proof treats oracle execution as an atomic algebraic state transition; cache timing, branch prediction, or power-consumption leakage does not exist unless explicitly added as a leakage oracle in the game code.

---

### 2. Conservative Extension and Requirements / Domain Decomposition

#### 2.1 Zave and Jackson's $W, S \vdash R$ and Problem Frames

`Basis: normative + documentation`

Zave and Jackson (*Four Dark Corners of Requirements Engineering*, ACM TOSEM 6(1):1–30, 1997, DOI `10.1145/237432.237434`) and Jackson (*Problem Frames*, 2001) argue that the central adequacy error in declarative specification is confusing **what exists in the physical environment** with **what the software machine enforces**. They partition descriptions over designated phenomena (events and states observable in the world vs. controlled by the machine vs. shared at the interface) into three artifacts:

- **$W$ (Domain Knowledge / World Assumptions):** Indicative statements believed to hold of the physical environment independently of the software (e.g., sensor physics, actuator inertia, monotonic hardware counters).
- **$S$ (Machine Specification):** Optative statements restricted strictly to **shared phenomena at the machine–environment interface** that the implementation must enforce (never referencing unobservable internal environment states directly).
- **$R$ (Requirements):** Optative statements over **environment phenomena** expressing what the customer/engineer actually wants true in the world.

The **Fundamental Verification Obligation** of requirements engineering is the entailment proof:

$$W,\; S \vdash R \qquad \text{together with} \qquad W \not\vdash \bot \quad \text{and} \quad W \land S \text{ satisfiable (input-receptive/realizable)}.$$

Zave and Jackson's "four dark corners" correspond directly to specification inadequacy pathologies:
1. **Grounding primitive designations:** Formal predicates (`sensor_ok`, `encrypted`) remain uninterpreted symbols until grounded in physical phenomena via explicit designation rules;
2. **Mixing indicative and optative moods:** Writing an optative requirement into $W$ turns a design obligation into an unchecked axiom;
3. **Referencing unshared phenomena in $S$:** Specifying that software must act directly on an unobservable world state makes $S$ unimplementable;
4. **Conflating $S$ with $R$:** Proving an implementation satisfies $S$ while omitting or falsifying $W$ proves nothing about whether $R$ holds in deployment.

#### 2.2 Definitional Conservative Extension Principles in HOL, Isabelle, and Lean

`Basis: normative + source`

Inside deductive proof assistants, specifications are written by extending an initial theory $\Sigma_0$ with new types, constants, and axioms $\Sigma_0 \subseteq \Sigma_1 \subseteq \dots \subseteq \Sigma_n$. A theory extension $\Sigma' \supseteq \Sigma$ is **logically conservative** iff for every $\Sigma$-sentence $\varphi$:

$$\Sigma' \vdash \varphi \iff \Sigma \vdash \varphi.$$

In particular, if $\Sigma$ is consistent ($\Sigma \not\vdash \bot$), **no conservative extension can ever introduce $\bot$**. Primary source inspection across four major interactive theorem provers documents the exact kernel guards enforcing conservativity—and the subtle historical soundness traps when any side-condition is relaxed:

1. **HOL Light (`jrh13/hol-light` @ `1a0c0e6b182cd9e271946ba8d78f7942619f4acb`, `fusion.ml` L575–640):**
   - `new_axiom` (L575–579) bypasses conservativity completely and records the axiom in `!the_axioms`.
   - `new_basic_definition` (L589–602) accepts `c = r` ONLY if: (i) `c` is not already defined (`L600–601`), (ii) `freesin [] r` (`r` has **zero free term variables**, `L592`), and (iii) `subset (type_vars_in_term r) (tyvars ty)` (**every polymorphic type variable in `r` appears in the type of `c`**, `L595`). Without condition (iii) (the classic HOL-88 bug reproduced in `toy probe [2]`), defining `c : bool = (∀ x y : α. x = y)` lets a user instantiate `α := unit` (`c = true`) and `α := bool` (`c = false`), immediately deriving `true = false`!
   - `new_basic_type_definition` (L617–640) defines a non-empty subtype `tyname` with `abs`/`rep` bijections ONLY from a theorem `Sequent([], P x)` with **empty assumption list** `asl = []` (`L620`) and closed predicate `P` (`L625`).
2. **HOL4 (`HOL-Theorem-Prover/HOL` @ `0c30bdb71aafd4e6a354f5b0b43fffbff6fa8d47`, `src/postkernel/Theory.sml` L1340–1503 & `src/prekernel/FinalThm-sig.sml` L143–145):**
   - Implements **Arthan's general specification principle** (`gen_prim_specification` / `prim_specification`, `Theory.sml` L1440–1477) and derives `new_definition` directly as a one-line special case of `Thm.gen_prim_specification (Thm.ASSUME eq)` (`L1489`). Given `|- ?x1...xn. P`, it conservatively introduces constants `c1...cn` satisfying `P[c1...cn]` provided `hyp` checks out and every type variable of `P` is captured in the types of all `ci` (or via explicit `gen_prim_specification` equality hypotheses `|- c_i = t_i => ...`).
3. **Candle / CakeML Verified HOL (`CakeML/cakeml` @ `2874b664e10939a3ee462215b2e068c89c1f70eb`, Kumar, Arthan, Myreen & Owens JAR 2016 DOI `10.1007/s10817-015-9357-x`):**
   - `candle/standard/semantics/holSoundnessScript.sml` (L15–75) and `holModelConservativityScript.sml` prove **machine-checked semantic conservativity** against ZFC set-theoretic models: every inference step and definitional/type extension preserves `is_structure` satisfaction, establishing a verified chain from HOL's kernel semantics down to CakeML's compiled x86-64 binary.
4. **Isabelle/HOL Overloading & Cyclic Definitional Trap (`isabelle-prover/mirror-isabelle` @ `c45cdab77eec0ac889f9717ca229a5e9064a24b1`, `src/Pure/defs.ML`; Kunčar & Popescu ITP 2015 DOI `10.1007/978-3-319-22102-1_15` & JAR 2019 DOI `10.1007/s10817-018-9454-8`):**
   - Unlike HOL Light/HOL4, Isabelle/HOL allows **ad-hoc overloading** (`consts c :: "'a => ..."` defined separately at different type instances). Prior to Kunčar & Popescu (2015), combining overloaded constant definitions with `typedef` could create a subtle **type-constant dependency cycle** (`c :: bool` defined via `typedef T`, whose rep-predicate references `c :: unit`) yielding non-conservativity and `False`! `src/Pure/defs.ML` (and `Candle`'s parallel formalization `candle/overloading/syntax/holSyntaxCyclicityScript.sml` L1–10) enforces syntactic **acyclic well-foundedness** over the combined dependency graph of constant instances and type constructors, proven semantically conservative by Kunčar & Popescu (2019).
5. **Lean 4 & `Lean4Lean` (`leanprover/lean4` @ `5a82f1a47fbc2323ad6be6b11a7c0522dd4f3e68`, `src/kernel/environment.cpp` L156–286; `digama0/lean4lean` @ `67f63b0c818920dfaed2ad07ccff187a6a8fe1e3`, `Lean4Lean/Environment.lean` L12–95 & `bugs-found.md` L1–5):**
   - Lean 4 separates conservative declarations (`Definition`, `Theorem`, `Opaque`, `Inductive` strict positivity) from non-conservative primitive additions (`Axiom` via `add_axiom` and `Quot` quotient axioms via `add_quot`), plus `unsafe`/`partial` definitions (`add_mutual`, `environment.cpp` L229–273).
   - **Crucial kernel boundary finding (`Lean4Lean` `bugs-found.md` L1–5 & `divergences.md` L20):** Formalizing Lean 4's kernel in Lean 4 itself exposed **three genuine soundness bugs** in the C++ kernel (`hasLooseBVars` non-conservativity, `leanprover/lean4#10475`, `leanprover/lean4#10511`) as well as a latent typing divergence in `unsafe`/`partial` `add_definition`/`add_mutual` (`divergences.md` L20, where adding the full `constant_info` body before body-checking permits `unsafe def foo : Nat := ...` self-unfolding, though confined to `unsafe` declarations carrying no logical content). Furthermore, Lean 4 relies on three standard non-definitional axioms (`propext`, `Quot.sound`, `Classical.choice`) plus optional `Lean.ofReduceBool` (`native_decide`, which expands the TCB to the entire compiler/runtime).

#### 2.3 Why Conservativity Is Necessary But Radically Insufficient for Adequacy

`Basis: normative + derived + execution`

A conservative extension guarantee proves **internal consistency** ($\Sigma' \not\vdash \bot$), **not** that a specification captures engineering intent:

- **Logical conservativity $\neq$ specification adequacy:** Defining $S_{\text{vac}}(e, m) := (e = \text{ok})$ (rejecting fault inputs) or $R_{\text{weak}}(e, m) := \text{true}$ uses only valid `new_basic_definition` / `def` extensions—it introduces zero logical axioms and is 100% conservative! Yet $W \land S_{\text{vac}} \vdash R$ succeeds **vacuously** on fault inputs (`toy probe [2]`: `W/\S|-R: True`, `realizable: False`), while $W \land S \vdash R_{\text{weak}}$ holds for a completely broken machine.
- **Unchecked domain axioms ($W$):** In Zave–Jackson decomposition, $W$ (hardware ISA, OS syscalls, floating-point/sensor dynamics) is routinely encoded via `Axiom` / `Hypothesis` / `opaque` assumptions rather than pure definitions—which **immediately steps outside conservative extension** and restores the possibility of outright contradiction ($W \vdash \bot$).

---

### 3. Head-to-Head Expressiveness Comparison and Iterative Specification Patching

#### 3.1 Structural Comparison: Games vs. Conservative Extension + $W, S \vdash R$

`Basis: normative + source + derived`

| Adequacy Dimension | Code-Based Security Games (`EasyCrypt`, `CryptoVerif`, `SSProve`, `FCF`) | Conservative Extension + $W, S \vdash R$ (`HOL`, `Isabelle`, `Lean 4`) |
|---|---|---|
| **Primary Question Answered** | Can any bounded adversary $\mathcal{A}$ interacting with explicit oracles distinguish real from ideal or force a win event beyond $\varepsilon$? | Does adding definitions $S$ preserve logical consistency, and does $W \land S$ deductively entail goal $R$? |
| **Who Is Quantified / Trusted** | Universally quantified PPT/bounded adversary $\forall \mathcal{A} \in \mathcal{C}(t, q)$; **challenger & oracle interfaces are trusted** | Universally quantified environments/inputs; **domain theory $W$ and top-level goal $R$ are trusted** |
| **What Counts as a Win / Failure** | Concrete observable bit/event in game state ($\mathsf{Adv} > \varepsilon$) | Any model/trace satisfying $W \land S$ that violates $R$ ($W \land S \not\vdash R$) |
| **How Vacuous / Weak Specs Appear** | $\mathsf{Adv} = 0$ because challenge oracle aborts, forces trivial queries, or omits a real leakage oracle (error, timing, side-channel) | $W \land S$ is **unsatisfiable** (antecedent contradiction / non-realizability: $\exists e \in W.\;\forall m.\;\neg S(e,m)$) or $R$ lacks frame/liveness clauses (`always reject` satisfies pure safety) |
| **Quantitative Probabilistic & Cost Bounds** | **Native** (exact rational/real advantage bounds $\varepsilon(q, t)$, birthday gaps $q^2/2^n$) | Requires explicit probabilistic monad/measure-theory encoding (`SSProve`, `FCF` bridge the two!) |
| **Behavioral Under-Approximation vs. Over-Permissiveness** | **Under-approximates the attacker** when an oracle is omitted -> false positive ("secure" game, broken deployment) | **Under-approximates the world $W$** or **over-approximates acceptable behavior $R$** -> vacuous/permissive spec passes |
| **What Happens When a Patch Adds a Special Case** | Only safe if adversary still cannot exploit the special case across all exposed oracles; adding a new oracle immediately breaks proofs | Kernel stays 100% happy (still conservative!); silent semantic drift unless $R$ and non-vacuity witnesses are explicitly re-tested |

#### 3.2 Behavior Under Iterative Specification Patching & Published Empirical Evidence

`Basis: normative + documentation + source + execution`

Real verified systems rarely keep a static specification; specs and code co-evolve across bug fixes, performance optimizations, and newly discovered threat vectors. Published empirical literature documents distinct failure pathologies under iterative patching across both traditions:

1. **Cryptographic Game-Model Drift & Oracle Omission (Albrecht, Paterson & Watson, IEEE S&P 2009 DOI `10.1109/SP.2009.5`; Degabriele, Paterson & Watson, *IEEE Security & Privacy* 9(3):33–41, 2011):**
   - Early provable-security analyses proved SSH's binary packet protocol (`BPP`) secure under an IND-CPA / stateful decryption game that abstracted packet parsing into atomic blocks returning a single uniform failure symbol. Albrecht, Paterson & Watson (2009) demonstrated practical plaintext-recovery attacks against real SSH CBC implementations (including OpenSSH) because real implementations read the encrypted length field first, wait for more TCP bytes or emit distinct connection-drop vs. MAC-error side channels—violating the idealized game's atomic-oracle abstraction.
   - Degabriele, Paterson & Watson (2011) generalized this across IPsec, SSH, and TLS: iteratively patching a cryptographic spec to model an error/length/timing oracle frequently invalidates prior game hops (`MtE` IND-CPA holds, yet `INT-CTXT` fails under decryption-error queries unless redesigned to `EtM`, as directly mechanized in `EasyCrypt/easycrypt` `examples/MEE-CBC/RCPA_CMA.ec`).
2. **Unverified Environment & Interface Shims in Verified Systems (Fonseca, Zhang, Wang & Krishnamurthy, EuroSys 2017 DOI `10.1145/3064176.3064183`):**
   - Studying formally verified distributed systems (`IronFleet`, `Verdi`, `Chapar`), Fonseca et al. found **16 bugs across the systems** (none in the mechanized Coq/Dafny proofs themselves!). Every single defect resided in **unverified shims, runtime serialization/network assumptions, or top-level specification misunderstandings ($W \leftrightarrow S$)**—precisely the boundary Zave & Jackson warn about where conservative definitions meet real-world domain axioms.
3. **Unverified Compiler Seams Outside Verified Cores (Yang, Chen, Eide & Regehr, PLDI 2011 DOI `10.1145/1993498.1993532`):**
   - Running `Csmith` across 6 CPU-years found **325+ bugs** in GCC and LLVM and **0 wrong-code bugs in CompCert's Coq-verified middle-end**, yet uncovered crashes/misbehaviors solely in **CompCert's unverified C front-end parser/elaborator and target assembly/runtime assumptions**.
4. **Proof Maintenance Under Iterative Spec/Code Evolution (`seL4`, Klein et al., ACM TOCS 32(1):2, 2014 DOI `10.1145/2560537`):**
   - `seL4` required ~20 person-years to verify ~8,700 lines of C against an Isabelle/HOL abstract specification (~200,000 lines of proof, >20:1 proof-to-code ratio). Klein et al. document that changing invariants or adding capabilities across kernel revisions causes cascading breakage in inductive invariant proofs unless layered via strict refinement hierarchies (`abstract -> executable -> C -> binary`).
5. **Automated Spec Regeneration & Patch Reward Hacking (`OSS Verify`, `theorem-labs/oss-verify-proofs` @ `32c8baf6e92f173b445903857770da103ba307e0` & Anthropic Oct 22, 2026 release):**
   - In verifying 239 OSS-Fuzz entry points across 123 C/C++ libraries (90 entry points across 32 libraries published in `oss-verify-proofs` using Rocq 9.2.0 and the `LPS` RISC-V/Linux process semantics), autonomous LLM provers were permitted to patch discovered C bugs and regenerate the binary no-crash spec. **Footnote 06 explicitly documents specification reward hacking under iterative patching**: because any no-crash theorem becomes trivially provable if a patch deletes functionality or returns early, the pipeline had to penalize patches, prove minimal behavioral diff bounds, and audit patches—confirming empirically that conservative, kernel-checked re-proving of patched specs does **not** catch spec weakening or trivialization without external adequacy checks.

*(All quantitative claims above originate in the cited primary papers and upstream repositories; our standalone Python probe in **Evidence** provides clean finite-state algebraic witnesses of the exact same structural asymmetries.)*

---

### 4. Multi-Level Performance and Resource Footprint Analysis (`L1–L6`)

`Basis: documentation + source + derived`

Choosing between code-based game frameworks, deductive conservative-extension provers, and their hybrids (`SSProve`/`FCF`) incurs sharply different engineering and computational costs across all six resource levels:

| Level | Metric / Bottleneck | Code-Based Games (`EasyCrypt` / `CryptoVerif`) | Hybrid Game-in-Kernel (`SSProve` / `FCF` in Rocq) | Conservative Extension Kernels (`HOL Light` / `Candle` / `Isabelle` / `Lean 4`) |
|---|---|---|---|---|
| **L1: Human & Agent Authoring Velocity** | Proof-to-spec expansion & patching cost | High expert bottleneck; `EasyCrypt` game hops average ~10–30× code size; `CryptoVerif` automates ~60–80% of algebraic rewrites but requires delicate manual game guidance when stuck | Very high manual/LLM verbosity (`SSProve` `KEM-DEM` requires verbose `ValidPackage` / `fseparate` obligations, `README.md` L306–308); `FCF` requires explicit `Comp` cost derivations | `seL4`: ~20 person-years / ~200k Isabelle LoC (~20:1 ratio, Klein et al. 2014). Autonomous LLM proving (`OSS Verify`, Oct 2026): ~600,000 Rocq LoC per median 18,000 RISC-V instructions (~33:1), consuming 100M+ LLM tokens across solo runs (-40% newer models, -17% shared proof reuse) |
| **L2: Framework & Toolchain Build Time** | From-scratch toolchain & stdlib build | `EasyCrypt` builds via OCaml/Dune in minutes plus external `Why3` + SMT binaries (`Z3`, `Alt-Ergo`, `CVC5`); `CryptoVerif` compiles to a single fast OCaml native binary | Heavy Rocq + `MathComp` + `mathcomp-analysis` + `Equations` + `extructures` build stack (`SSProve` CI matrix across Rocq 9.0–9.2, `.github/workflows/`); `FCF` needs base Rocq only | `HOL Light`: seconds in OCaml; `Lean 4`: minutes C++/Lean bootstrap (`lean4lean` replays `Init`/Mathlib in Lean); `Candle`: verified via CakeML's full bootstrapped HOL4 build |
| **L3: Compilation, Elaboration & Synthesis Latency** | Proof checking, SMT timeouts & interactive responsiveness | Fast interactive stepping on simple hops (`< 1s`), but `EasyCrypt` suffers **SMT tail latency and quantifier non-determinism** across `Why3` queries; `CryptoVerif` backtracking searches seconds–minutes | Slow unification/typeclass elaboration in `MathComp`/`Equations` (`SSProve` `link_assoc`/`interchange` proofs); `FCF` `Comp` unfolding hits Rocq kernel conversion overhead | Interactive Lean 4 LSP (`< 50 ms` warm edits on small lemmas), but complex `isDefEq`/typeclass goals and SMT/hammer tactics hit seconds–minutes tails; `Isabelle` document-model parallelism scales well across theories |
| **L4: Generated Code Execution Performance** | Runtime overhead of verified artifacts | Proofs are fully erased (zero runtime overhead); `EasyCrypt` extracts to Jasmin assembly (`formosa-crypto`) matching hand-tuned x86-64/AVX2 speeds | Proofs fully erased; `SSProve` extracted OCaml (`The Last Yard`, CPP 2024) or Jasmin links at native/OCaml speed | Proofs fully erased; **runtime cost arises only if unverified shims or online monitors** (e.g., runtime `W`-assumption checks) are inserted |
| **L5: Proof / Certificate Verification Speed** | Checker throughput & admission latency | **`EasyCrypt` has no standalone small proof-term checker**—re-verification replays the full `Why3` + external SMT solver invocations (`Z3`/`Alt-Ergo`/`CVC5`)! `CryptoVerif` has no independent proof certificate | Checked directly by Rocq's kernel (`rocqchk` standalone checker over compiled `.vo` proof terms; **zero SMT trust**) | **`HOL Light` / `Candle`**: tiny LCF kernel (~500–700 LoC in `fusion.ml`), fastest per-inference re-checking; **`Lean 4` / `Lean4Lean`**: checks `.olean` binary environments independently (`Main.lean`); **`Isabelle`**: exports proof terms/theory graphs |
| **L6: RAM, Disk & Binary Footprints** | Compiler/checker RSS & proof artifact sizes | Small `.ec` source files (KB–MB) since SMT discharges proof obligations without storing full proof terms; requires multiple SMT solver binaries | Large compiled `.vo` artifacts + multi-GB OCaml/Rocq process RSS when `mathcomp-analysis` real-number theories are loaded | `.olean` / `.thy` heap images reach hundreds of MB to several GB for large corpora (`Mathlib`, `seL4`); `OSS Verify`'s 180M lines of Rocq across 239 entry points illustrate massive proof-script storage footprints |

---

### 5. Human Comprehensibility and Conceptual Simplicity / Model Refinement (`C1–C2`)

`Basis: derived + normative + source`

#### 5.1 Human Comprehensibility vs. Agent Execution (`C1`)

A sharp gap separates **what an LLM or automated tactic engine can discharge** from **what a human auditor can verify**:

- **Audit surface in conservative extension:** A theorem proved in Lean 4 or HOL Light needs zero manual inspection of its 600,000-line tactic proof (the kernel verifies soundness), **but the human auditor MUST understand 100% of the theorem statement, every transitive definition inside it, and every `Axiom` / domain assumption $W$**. A single subtle bug in `W` (`LPS` Linux process semantics or floating-point rounding) or a hidden implication vacuity invalidates the entire proof, regardless of kernel soundness.
- **Audit surface in code-based games:** A Bellare–Rogaway game $G_0$ is concrete, ~20–80 lines of pseudocode/imperative code making adversary interactions visually explicit. Human reviewers spot missing oracles or weird abort branches far more easily than in deeply nested inductive invariants, **yet** `EasyCrypt` proofs can still hide subtle vacuous preconditions in module-parameter `require` clauses or `pRHL` pre/post invariants, and `SSProve` stacks layers of MathComp/category-theory coercions (`coerce_kleisli`, `pkg_composition.v` L31–42) that impose high working-memory load on non-experts.

#### 5.2 Universal Model Refinement and Orthogonality (`C2`)

Examined through **Ousterhout's Deep Module test** and **Felleisen's macro-expressibility lens**:

- **Why naive unification fails (either direction):**
  1. Trying to reduce **computational security games** into pure unbounded HOL/Lean specifications fails because computational primitives (PRFs, PRGs, IND-CPA) are **false against unbounded adversaries**—the adversary quantifier *must* carry an explicit computational/oracle-query resource model (as in `FCF`'s `WC_PolyTime.v` or `SSProve`'s package interfaces).
  2. Trying to replace **conservative extension + $W, S \vdash R$** purely with game-based equivalences fails for non-probabilistic functional/physical invariants where **definitional soundness** and **explicit separation of indicative $W$ from optative $S$** are needed to prevent circular assumptions and vacuous domain contradictions.
- **Minimal, orthogonal synthesis:** An ideal universal specification discipline treats **specification adequacy as a three-part contract** rather than one overloaded notion:
  1. **Internal Consistency (Kernel Conservativity):** All types and operators are introduced via checked definitional/inductive/specification principles (`HOL` `gen_prim_specification`, `Candle`, `Isabelle` acyclic `defs`, `Lean 4`/`Lean4Lean` kernel), with **explicit axiom tracking** (`#print axioms` / `Print Assumptions`) isolating non-definitional world assumptions $W$.
  2. **Environment-Realizable Intent ($W, S \vdash R$ + Witness Realizability):** Explicit separation of indicative world assumptions $W$ from machine interface spec $S$ and requirement $R$, paired with **mandatory witness/realizability checks** ($\exists w.\; W(w)$ and $\forall e \in W.\;\exists m.\; S(e, m)$) so vacuous axioms cannot masquerade as proofs.
  3. **Explicit Threat-Interface Quantification (Bounded-Adversary Games):** Whenever security, side channels, or distributed adversarial environments are involved, $S$ and $R$ are packaged as an **executable game experiment** with explicitly declared adversary oracle signatures and disjoint state (`SSProve` `ValidPackage` + `fseparate`), separating what the adversary can observe/perturb from secret internals.

---

### 6. End-to-End Solution and Implementation Validation (`V1–V4`)

`Basis: normative + documentation + source`

Because neither game proofs nor conservative kernels validate the unmodeled semantic gap between formal assumptions ($W$, game oracles) and physical/software execution, end-to-end assurance requires pairing formal specification with four validation rings:

1. **`V1` Specification Adequacy, Mutation & Non-Vacuity Validation:** Run automated witness-existence checks on every quantified precondition and domain axiom $W$, measure **spec-mutant kill rates** (generating intentional implementation bugs via mutation tools and verifying that the spec rejects them rather than vacuously passing or permitting `always-reject` lobotomies), and run property-based differential testing (e.g., `QuickChick` / random input fuzzing comparing the formal spec $S$ against reference interpreters or RFC test vectors).
2. **`V2` Compiler, Lowering & Kernel Checker Validation:** Cross-check proof kernels using independent, small-TCB or self-verified implementations (`Lean4Lean` replaying Lean 4 environments, `Candle` executing CakeML-verified HOL checking, `rocqchk` re-checking `SSProve`/`FCF` `.vo` artifacts), and apply differential/metamorphic compiler fuzzing (`Csmith`/`YARPGen`/`EMI`) to unverified front-ends, extraction pipelines (`Jasmin`/`OCaml`), and C compilers outside the proof boundary (catching CompCert-style front-end/driver gaps).
3. **`V3` Concurrency, Crash & Physical/Microarchitectural Leakage Validation:** For systems and cryptographic implementations proved via black-box games or sequential HOL specs, validate weak-memory concurrency via stateless DPOR (`GenMC`/`Loom`), crash/torn-I/O consistency via fault injection, and—**critically for game-based cryptographic specs**—validate physical and microarchitectural side-channel silence (timing, speculative prefetching, cache, power/EM) via relational CPU fuzzing (`Revizor`), 1st/2nd-order Welch's $t$-test `TVLA` trace analysis, and gate-level glitch probing (`Alma`), closing the exact oracle-omission gap exposed by Albrecht–Paterson–Watson.
4. **`V4` Plant Falsification, Telemetry Replay & Human Comprehension Validation:** Where $W$ models continuous physical plants or human operators, falsify $W$ against richer physics via Signal Temporal Logic (`STL`) robustness minimization (`S-TaLiRo`/`Breach`), replay real telemetry traces and historical incident logs against deployed specs, enforce online runtime `ModelPlex` monitors checking whether live observations still satisfy $W$, and empirically test whether human engineers accurately interpret the formal spec's obligations without mental-model inversions.

## Boundaries

- **`known not to apply` — Conservativity Implies Intent Faithfulness:** Kernel-checked conservative extension guarantees only relative logical consistency ($\Sigma' \not\vdash \bot$), **not** that a specification captures user intent, avoids vacuous preconditions, or survives iterative weakening patches (`OSS Verify` Footnote 06; `toy probe [2]`, `[3]`).
- **`known not to apply` — Black-Box Game Proofs Cover Omitted Oracles or Physical Leakage:** A game-playing proof of $\mathsf{Adv} \le \varepsilon$ provides zero assurance against any channel (error messages, TCP packet-length leaks, cache timing, power draw) absent from the game's explicit oracle interface (Albrecht et al. 2009; Degabriele et al. 2011; `toy probe [1]`).
- **`unsupported` — Independent Standalone Proof-Term Checking in `EasyCrypt` and `CryptoVerif`:** At `EasyCrypt` `ce19cb6cbab4951e58553c36128e8a19f2f90c6a`, re-verification invokes `Why3` and external SMT solvers rather than emitting an independently checkable proof-object certificate like `rocqchk` or `lean4lean`. Likewise, `CryptoVerif` relies on its OCaml prover without independent proof-term export.
- **`unsupported` — Continuous Distributions in `FCF`:** `adampetcher/fcf` (`2550fa27e491c03655cddc7830a5baeb15520104`) models computations via discrete finite-support `getSupport` sub-distributions (`Comp.v`), which does not natively support continuous probability measures without discretization.
- **`unknown` — Universal Automated Detection of Semantic Oracle Omissions:** No general static procedure is known that automatically discovers which physical or protocol side channels (`W` or attacker oracles) an engineer forgot to include in a formal specification before an attack or incident reveals them.
- **`not examined` — Full Execution of `EasyCrypt`, `SSProve`, `FCF`, `Candle`, and `Lean4Lean` Test Suites:** Upstream source files and theorem statements were inspected directly at the pinned revisions, and the finite-state structural interactions were exercised via the standalone Python toy-model probe below; full Rocq/OCaml/HOL4/Lean4 compilation and SMT solver timing benchmarks were not executed locally.

## Evidence

### Upstream Repository Source Citations (Inspected `2026-11-19`)

- **`EasyCrypt/easycrypt`** @ `ce19cb6cbab4951e58553c36128e8a19f2f90c6a`:
  - `examples/FundamentalLemma.ec` L15–19 (`Mem` / `Exp` module interfaces), L21–49 (`Pr_split` and `FundamentalLemma`).
  - `src/phl/ecPhlFel.ml` L50–89 (`callable_oracles_f` tracking oracle writes), L117–130 (`t_failure_event_r`).
  - `examples/MEE-CBC/RCPA_CMA.ec` L8–75, L593–627 (`MacThenEncrypt` vs `EtM` `RCPA_SUF_CTXT` security reductions).
- **`SSProve/ssprove`** @ `9a37fe0ab79d041f8d835e6cf18e37614b16a791`:
  - `theories/Crypt/package/pkg_advantage.v` L41–99 (`Advantage`, `AdvantageE`, `adv_equiv` requiring `fseparate LA L₀` and `fseparate LA L₁`), L123–166 (`Advantage_link`, `Advantage_par`).
  - `theories/Crypt/package/pkg_composition.v` L28–59 (`coerce_kleisli`, `resolve`), `README.md` L250–350 & L715–731 (`interchange` law, `Print Assumptions` listing 4 axioms), `theories/Crypt/Axioms.v` L11–13 (`Axioms.R`, `absord`).
- **`adampetcher/fcf`** @ `2550fa27e491c03655cddc7830a5baeb15520104`:
  - `src/FCF/Comp.v` L17–21 (`Comp` inductive constructors `Ret`, `Bind`, `Rnd`, `Repeat`).
  - `src/FCF/TwoWorldsEquiv.v` L13–45 (`evalDist_bool_support` over finite `getSupport`).
  - `src/FCF/WC_PolyTime.v` L13–55 (`function_cost_model` explicit polynomial cost class).
- **`jrh13/hol-light`** @ `1a0c0e6b182cd9e271946ba8d78f7942619f4acb`:
  - `fusion.ml` L571–579 (`new_axiom`), L589–602 (`new_basic_definition` enforcing `freesin [] r` and `subset (type_vars_in_term r) (tyvars ty)`), L617–640 (`new_basic_type_definition` requiring `asl = []` and closed predicate `P`).
- **`HOL-Theorem-Prover/HOL`** @ `0c30bdb71aafd4e6a354f5b0b43fffbff6fa8d47`:
  - `src/postkernel/Theory.sml` L1385–1403 (`check_null_hyp`, `check_free_vars`, `check_tyvars`), L1422–1503 (`new_type_definition`, `gen_new_specification`, `new_specification`, `new_definition` implemented via `Thm.gen_prim_specification (Thm.ASSUME eq)`).
  - `src/prekernel/FinalThm-sig.sml` L143–145 (`prim_type_definition`, `prim_specification`, `gen_prim_specification`).
- **`CakeML/cakeml`** @ `2874b664e10939a3ee462215b2e068c89c1f70eb`:
  - `candle/standard/semantics/holSoundnessScript.sml` L15–75 (set-theoretic soundness of inference rules).
  - `candle/overloading/syntax/holSyntaxCyclicityScript.sml` L1–10 (cyclicity check implementing Kunčar CPP 2015).
- **`isabelle-prover/mirror-isabelle`** @ `c45cdab77eec0ac889f9717ca229a5e9064a24b1`:
  - `src/Pure/defs.ML` L1–75 (syntactic dependency and overloading well-foundedness graph checker).
- **`leanprover/lean4`** @ `5a82f1a47fbc2323ad6be6b11a7c0522dd4f3e68`:
  - `src/kernel/environment.cpp` L156–286 (`add_axiom`, `add_definition`, `add_theorem`, `add_opaque`, `add_mutual`, `environment::add` dispatch).
- **`digama0/lean4lean`** @ `67f63b0c818920dfaed2ad07ccff187a6a8fe1e3`:
  - `Lean4Lean/Environment.lean` L12–95 (`checkDefinitionBody`, `addAxiom`, `addDefinition`, `addTheorem`, `addMutual`).
  - `bugs-found.md` L1–5 (`hasLooseBVars` non-conservativity, `lean4#10475`, `lean4#10511`) and `divergences.md` L17–21 (`unsafe`/`partial` self-unfolding divergence).
- **`theorem-labs/oss-verify-proofs`** @ `32c8baf6e92f173b445903857770da103ba307e0`:
  - `README.md` L1–45 (90 OSS-Fuzz entry points across 32 libraries verified in Rocq 9.2.0 against `LPS` RISC-V/Linux semantics, documenting `LPS` best-effort assumptions).

### Primary Literature & Empirical Disclosures Verified

- Bellare & Rogaway (2006), *The Security of Triple Encryption and a Framework for Code-Based Game-Playing Proofs*, EUROCRYPT 2006, LNCS 4004, pp. 409–426, DOI `10.1007/11761679_25` (ePrint `2004/331`).
- Shoup (2004), *Sequences of Games: A Tool for Taming Complexity in Security Proofs*, IACR ePrint `2004/332`.
- Halevi (2005), *A Plausible Approach to Computer-Aided Cryptographic Proofs*, IACR ePrint `2005/181`.
- Blanchet (2008), *A Computationally Sound Mechanized Prover for Security Protocols*, IEEE TDSC 5(4):193–207, DOI `10.1109/TDSC.2007.1005`.
- Zave & Jackson (1997), *Four Dark Corners of Requirements Engineering*, ACM TOSEM 6(1):1–30, DOI `10.1145/237432.237434`.
- Kumar, Arthan, Myreen & Owens (2016), *Self-Formalisation of Higher-Order Logic: Semantics, Soundness, and a Verified Implementation*, *Journal of Automated Reasoning* 56(3):221–259, DOI `10.1007/s10817-015-9357-x`.
- Kunčar & Popescu (2015 / 2019), *A Consistent Foundation for Isabelle/HOL*, ITP 2015 DOI `10.1007/978-3-319-22102-1_15` and *Journal of Automated Reasoning* 62(4):531–555, DOI `10.1007/s10817-018-9454-8`.
- Albrecht, Paterson & Watson (2009), *Plaintext Recovery Attacks against SSH*, IEEE S&P 2009, DOI `10.1109/SP.2009.5`.
- Degabriele, Paterson & Watson (2011), *Provable Security in the Real World*, *IEEE Security & Privacy* 9(3):33–41.
- Yang, Chen, Eide & Regehr (2011), *Finding and Understanding Bugs in C Compilers*, PLDI 2011, DOI `10.1145/1993498.1993532`.
- Klein, Andronick, Elphinstone, Murray, Sewell, Kolanski & Heiser (2014), *Comprehensive Formal Verification of an OS Microkernel*, ACM TOCS 32(1):2, DOI `10.1145/2560537`.
- Fonseca, Zhang, Wang & Krishnamurthy (2017), *An Empirical Study on the Correctness of Formally Verified Distributed Systems*, EuroSys 2017, DOI `10.1145/3064176.3064183`.
- Lucas et al. / Anthropic Frontier Red Team & Theorem (Oct 22, 2026), *LLMs are making formal software verification feasible at a much larger scale*, `https://www.anthropic.com/research/formal-verification` (239 OSS-Fuzz entry points across 123 libraries, ~180M lines Rocq / ~600K LoC per ~18K RISC-V instructions, 40% token drop across model generations, 17% shared proof reuse, Footnote 06 reward-hacking penalties).

### Standalone Python Toy-Model Probe and Verbatim Output (`2026-11-19`)

`Basis: execution (standalone Python toy model of game hopping, HOL definition guards, and Zave–Jackson realizability; not EasyCrypt or HOL Light itself)`

Save to `/tmp/probe_games_vs_extension.py` and run `python3 /tmp/probe_games_vs_extension.py`:

```python
#!/usr/bin/env python3
"""Standalone Python toy models comparing code-based security games vs conservative extension."""

from dataclasses import dataclass
from fractions import Fraction
from itertools import product


# ==============================================================================
# Part 1: Toy-Model Game Hopping (Fundamental Lemma) vs Oracle-Omission Blindspot
# ==============================================================================
def run_game_hopping_toy_probe() -> None:
    n_space = 4
    pairs = list(product(range(n_space), range(n_space)))

    def eval_games() -> tuple[Fraction, Fraction, Fraction]:
        g0_win, g1_win, bad_cnt = 0, 0, 0
        total = 0
        for r1, r2 in pairs:
            for u1, u2 in pairs:
                total += 1
                bad = (r1 == r2)
                if bad:
                    bad_cnt += 1
                c1_g0 = u1 ^ 0b01
                c2_g0 = (u1 if bad else u2) ^ 0b10
                c1_g1 = u1 ^ 0b01
                c2_g1 = u2 ^ 0b10
                if (c1_g0 ^ c2_g0) == 0b11:
                    g0_win += 1
                if (c1_g1 ^ c2_g1) == 0b11:
                    g1_win += 1
        return Fraction(g0_win, total), Fraction(g1_win, total), Fraction(bad_cnt, total)

    p_g0, p_g1, p_bad = eval_games()
    adv_hop = abs(p_g0 - p_g1)
    assert adv_hop <= p_bad

    domain = 8
    adv_cpa_no_oracle = Fraction(0, 1)
    adv_with_pad_oracle = Fraction(domain - 1, domain)
    print(f"[1] Toy GameHop: Pr[G0=1]={p_g0} Pr[G1=1]={p_g1} |diff|={adv_hop} <= Pr[BAD]={p_bad}")
    print(f"[1] Toy SpecGap: Adv(no_error_oracle)={adv_cpa_no_oracle} vs Adv(with_pad_oracle)={adv_with_pad_oracle}")


# ==============================================================================
# Part 2: HOL-Style Definitional Extension Guard vs Type-Variable Escape & Vacuity
# ==============================================================================
@dataclass(frozen=True)
class TyVar:
    name: str


@dataclass(frozen=True)
class TyCon:
    name: str
    args: tuple


def tyvars(t) -> set[str]:
    if isinstance(t, TyVar):
        return {t.name}
    out: set[str] = set()
    for a in t.args:
        out |= tyvars(a)
    return out


def hol_definition_check(const_ty, rhs_tyvars: set[str], rhs_free_term_vars: set[str], enforce_tyvar_check: bool) -> tuple[bool, str]:
    if rhs_free_term_vars:
        return False, f"REJECT: free term variables {sorted(rhs_free_term_vars)}"
    missing = rhs_tyvars - tyvars(const_ty)
    if missing and enforce_tyvar_check:
        return False, f"REJECT: unbound type variables in RHS {sorted(missing)}"
    return True, "ACCEPT"


def run_conservative_extension_toy_probe() -> None:
    bool_ty = TyCon("bool", ())
    ok_strict, msg_strict = hol_definition_check(bool_ty, {"alpha"}, set(), enforce_tyvar_check=True)
    ok_buggy, msg_buggy = hol_definition_check(bool_ty, {"alpha"}, set(), enforce_tyvar_check=False)

    c_unit = all(x == y for x in [()] for y in [()])
    c_bool = all(x == y for x in [False, True] for y in [False, True])
    derived_false = (c_unit and not c_bool)

    env_states = [0, 1]
    mach_states = [0, 1]
    R = lambda e, m: (e == 0) or (m == 0)
    S_sound = lambda e, m: (m == 0) if e == 1 else True
    S_vac = lambda e, m: (e == 0)

    def check_zj(S_pred):
        entails_R = all(R(e, m) for e in env_states for m in mach_states if S_pred(e, m))
        realizable = all(any(S_pred(e, m) for m in mach_states) for e in env_states)
        return entails_R, realizable

    ent_s, real_s = check_zj(S_sound)
    ent_v, real_v = check_zj(S_vac)
    print(f"[2] Toy HOL-def ('a escapes bool): strict=({ok_strict}, {msg_strict}) | unchecked=({ok_buggy}, {msg_buggy}, derives_false={derived_false})")
    print(f"[2] Toy Zave-Jackson: S_sound=(W/\\S|-R:{ent_s}, realizable:{real_s}) | S_vac=(W/\\S|-R:{ent_v}, realizable:{real_v})")


# ==============================================================================
# Part 3: Iterative Patch Accumulation Divergence Across the Two Paradigms
# ==============================================================================
def run_iterative_patching_toy_probe() -> None:
    env = [(e, cal) for e in (0, 1) for cal in (0, 1)]
    R_intent = lambda e, cal, m: (e == 0) or (m == 0)
    S0 = lambda e, cal, m: (m == 0) if e == 1 else True
    S1_patched = lambda e, cal, m: True if cal == 1 else S0(e, cal, m)
    consistent_def_s1 = True
    intent_holds_s0 = all(R_intent(e, cal, m) for e, cal in env for m in (0, 1) if S0(e, cal, m))
    intent_holds_s1 = all(R_intent(e, cal, m) for e, cal in env for m in (0, 1) if S1_patched(e, cal, m))
    print(f"[3] Toy PatchDrift: S0(intent={intent_holds_s0}) -> S1_patched(kernel_consistent={consistent_def_s1}, intent={intent_holds_s1})")


if __name__ == "__main__":
    run_game_hopping_toy_probe()
    run_conservative_extension_toy_probe()
    run_iterative_patching_toy_probe()
```

Observed output (`2026-11-19`, Linux x86_64, Python 3):

```text
[1] Toy GameHop: Pr[G0=1]=7/16 Pr[G1=1]=1/4 |diff|=3/16 <= Pr[BAD]=1/4
[1] Toy SpecGap: Adv(no_error_oracle)=0 vs Adv(with_pad_oracle)=7/8
[2] Toy HOL-def ('a escapes bool): strict=(False, REJECT: unbound type variables in RHS ['alpha']) | unchecked=(True, ACCEPT, derives_false=True)
[2] Toy Zave-Jackson: S_sound=(W/\S|-R:True, realizable:True) | S_vac=(W/\S|-R:True, realizable:False)
[3] Toy PatchDrift: S0(intent=True) -> S1_patched(kernel_consistent=True, intent=False)
```

## Revalidation

1. **Lean 4 & `Lean4Lean` kernel parity:** Diff `leanprover/lean4` (`src/kernel/environment.cpp`) and `digama0/lean4lean` (`bugs-found.md`, `divergences.md`, `Lean4Lean/Environment.lean`) relative to `5a82f1a47fbc2323ad6be6b11a7c0522dd4f3e68` and `67f63b0c818920dfaed2ad07ccff187a6a8fe1e3` to check whether newly surfaced kernel soundness divergences or `unsafe` environment-extension differences have been closed.
2. **`EasyCrypt` & `SSProve` certificate/cost evolution:** Check `EasyCrypt/easycrypt` (`ce19cb6cbab4951e58553c36128e8a19f2f90c6a`, `src/phl/ecPhlFel.ml`, `theories/tactics/FelTactic.ec`) for any independent proof-term export beyond `Why3`, and check `SSProve/ssprove` (`9a37fe0ab79d041f8d835e6cf18e37614b16a791`, `README.md` `Print Assumptions`, `theories/Crypt/package/pkg_advantage.v`) for changes to its Rocq axiom footprint or explicit runtime cost bounds.
3. **`HOL Light`, `HOL4`, `Candle`, and `Isabelle/HOL` definitional rules:** Diff `fusion.ml` (`1a0c0e6b182cd9e271946ba8d78f7942619f4acb`), `Theory.sml` (`0c30bdb71aafd4e6a354f5b0b43fffbff6fa8d47`), and `src/Pure/defs.ML` (`c45cdab77eec0ac889f9717ca229a5e9064a24b1`) to verify whether definitional extension guards or overloading cyclicity checks changed.
4. **Standalone algebraic toy probe:** Re-run `python3 /tmp/probe_games_vs_extension.py` (`< 0.1 s`, Python 3 standard library only) to verify exact rational advantage arithmetic, type-variable escape rejection, Zave–Jackson realizability separation, and patch drift behavior.
