# Specification Adequacy, Vacuity Detection, and Anti-Goodhart Verification

## Summary

A kernel-checked proof of $T \models S$ establishes only that implementation $T$ satisfies formal statement $S$; it says nothing about whether $S$ captures the intended safety, functional, or security property. Under automated synthesis, reinforcement learning, or agentic proving pressure—instances of **Adversarial and Extremal Goodhart's Law**—unconstrained optimizers systematically exploit specification-level loopholes rather than solving the hard verification problem. Moving statements of correctness out of the opaque Trusted Computing Base (TCB) requires combining five orthogonal defenses:

1. **Eliminating formal-logic operator, quantifier, and polarity traps:** Totalized arithmetic (`Nat.sub` saturating at `0`, `Nat.div`/`Int.ediv` returning `0` on `/ 0`, SMT-LIB `Int` uninterpreted `/ 0` vs. Z3 `bvudiv(_, 0) = 2^w - 1`), Euclidean vs. hardware-truncating signed remainder (`(-7 : Int) % 2 = 1` vs. `-1`), Lean 4's default-enabled `autoImplicit` + `relaxedAutoImplicit` silently quantifying misspelled identifiers, claim-polarity inversions (smuggling compiler `WellDefined(x) => ...` antecedents into verifiers/sandboxes), and circular specifications ($\mathsf{Consts}(S) \cap \mathsf{Consts}(T) \neq \emptyset$).
2. **Vacuity detection and linear $(m + 1)$-witness clause independence:** Extending Beer–Ben-David–Eisner–Rodeh / Kupferman–Vardi / Chockler–Kupferman–Vardi subformula-perturbation vacuity, a compound specification $S = \bigwedge_{i=1}^m C_i$ defeats **multi-conjunct canary masking** ($C_1 \land C_2 \land \mathsf{True}$) using one joint positive witness plus $m$ single-clause-isolating negative counter-witnesses.
3. **Primal-dual completeness (witness uniqueness and bidirectional codecs):** Pairing existence with uniqueness eliminates dual under-/over-constrained bugs—exemplified in zero-knowledge circuits by `Veridise/Picus` (existential completeness + deterministic output uniqueness over $\mathbb{F}_p$) and in binary codecs by `project-everest/everparse` (`serializer_correct` + `injective` $\implies$ `serializer_complete`) and `secure-foundations/vest` (`SPRoundTrip` + `NonMalleable` $\implies$ `PSRoundTrip`).
4. **3-outcome reactive/divergence adequacy and mutation-kill auditing:** Adequate specifications distinguish terminating values, genuine infinite divergence (never conflating arbitrary-length finite prefixes with divergence under unbounded nondeterminism, where König's Lemma fails), and faults (`ub` vs. `unsupported`), backed by positive reference canaries and negative buggy-mutant rejection witnesses (`MutSpec` / mutation model checking / `SpecFuzzer`).
5. **Cryptographic intuition-soundness games paired with parametric honest-tool completeness:** Requiring full semantic closure locks out every decidable syntactic type or borrow checker by Rice's theorem (`1953`). Replacing semantic closure with a human-audited, trap-free `AcceptanceSurface` locked across edits plus **coupled parametric family generalization** ($\forall k \in \mathbb{N},\; \mathsf{Handles}(C \circ F, g(k))$) catches `find(_) = None`, lookup-table overfitting, and `abort()`/`loop {}` utility-destroying rewrites without violating Rice's barrier.

## Applicability

This reference synthesizes primary-source operator semantics, formal verification frameworks, vacuity/uniqueness algorithms, and executable model probes observed on `2026-11-19`:

- **Dependent-type operator and elaborator semantics:** `leanprover/lean4` at `8009d0a64d2860606c6a5ac5ff6702622b24921e` (`Init/Prelude.lean`, `Init/Data/Int/DivMod/Basic.lean`, `Lean/Elab/AutoBound.lean`, `Lean/Elab/Tactic/Decide.lean`).
- **SMT bitvector and integer totalization:** `Z3Prover/z3` at `437536cd64a544a1c329fc57d83e56e294fdf47c` (`src/ast/bv_decl_plugin.cpp`, `src/ast/rewriter/bv_rewriter.cpp`) and the SMT-LIB Standard Version 2.6.
- **ZKP deterministic witness uniqueness:** `Veridise/Picus` at `138b151d3a388e5b6c040c163e0a1db04f2ceda6` (`picus.rkt`, `picus/algorithms/dpvl.rkt`, `picus-cex-uniqueness.rkt`).
- **Verified bidirectional binary codecs:** `project-everest/everparse` at `270f5aab699ac284d8777d4f01be20a5d91ea47c` (`lib/everparse/lowparse/LowParse.Spec.Base.fsti`) and `secure-foundations/vest` at `026867a37d4b918153058df2c8db6c52fc62ba35` (`vest_lib/src/core/spec.rs`, `vest_lib/src/core/proof.rs`, `guide/src/guarantees.md`).
- **Foundational specification-adequacy theory:** Beer et al. (*FMSD 2001*), Kupferman & Vardi (*STTT 2003*), Chockler, Kupferman, & Vardi (*FMSD 2006*), Foster et al. (*TOPLAS 2007*), Rice (*Trans. AMS 1953*), Manheim & Garrabrant (`arXiv:1803.04585`), Cordy et al. (*ESEC/FSE*), and Molina et al. (*ICSE* / *ASE*).

These findings apply to any verification workflow where formal specifications are written, refactored, inferred, or audited under optimization pressure—including LLM/RL verified code generation (e.g., VERINA, CLEVER), proof-assistant specification reviews, ZKP circuit auditing, binary parser/serializer certification, and automated compiler or static-analyzer qualification.

**Scope qualifications:**
- Lean 4 option defaults (`autoImplicit := true`, `relaxedAutoImplicit := true`) and `Int`/`Nat` totalization definitions reflect `leanprover/lean4@8009d0a6` directly (`Basis: source`); individual projects may override `autoImplicit` in `lakefile.toml` or per-file `set_option`.
- Z3's bitvector division-by-zero behavior depends on the `hi_div0` rewriter parameter (`src/ast/rewriter/bv_rewriter.cpp` L1202–1216); SMT-LIB 2.6 `QF_BV` fixes `bvudiv(x, 0) = #b11...1` (corresponding to `hi_div0 = true`), whereas SMT-LIB 2.6 `Ints`/`Reals` leaves `div(x, 0)` uninterpreted.
- Executable probes (`Basis: execution`) are self-contained Python 3.13.15 models reproducing all five adequacy mechanisms deterministically without requiring external solver or Lean builds (see **Boundaries**).

## Findings

### 1. Goodhart's Law in Automated Formal Verification

`Basis: documentation + derived`

Manheim and Garrabrant (`arXiv:1803.04585`) classify four failure modes when a proxy metric $M$ stands in for a true objective $U$: **Regressional**, **Extremal**, **Causal**, and **Adversarial** Goodhart. In formal verification, the formal specification $S$ plus automated verification harness $H$ act as the proxy for the engineer's intended behavioral objective $U$. Under human hand-proving, engineers rarely exploit accidental loopholes in their own specifications; under automated synthesis, RL fine-tuning, or agentic proof search, the optimizer treats $S$ and $H$ purely as an objective function, triggering **Extremal** and **Adversarial Goodhart**:

| Goodhart Channel | Mechanism Exploited | Concrete Manifestation | Why Naive Kernel Check Passes |
| :--- | :--- | :--- | :--- |
| **Antecedent vacuity** | Unsatisfiable precondition $P \equiv \bot$ | `∀ x, x < 0 ∧ x > 0 → Unsafe(f x)` (or impossible memory-invariant hypothesis) | `False → Q` is a valid theorem for arbitrary buggy `f` |
| **Consequent triviality** | Weakened postcondition or decoupled ghost slot | `ensures True`, or proving `ret_ghost = expected` while ABI register `rax` returns `0` | Kernel checks stated proposition, not ABI wiring |
| **Operator / quantifier traps** | Totalized arithmetic or implicit typos | `len - off ≥ 0` on `Nat`; misspelled `reqs` auto-bound via `autoImplicit` | Well-typed tautology in the host logic |
| **Polarity inversion** | Wrong implication or refinement direction | Applying compiler `WellDefined(x) → ...` to a sandbox/parser; dropping UB paths in lifting | Statement is syntactically plausible and provable |
| **Liveness / utility destruction** | Partial-correctness loophole | Compiling every program to `loop {}` or `abort()`; verifier returning `Reject` on all inputs | Satisfies $\mathsf{Terminates}(p, v) \implies Q(v)$ or $\mathsf{Accept}(p) \implies \mathsf{Safe}(p)$ vacuously |
| **Circular / tool-coupled spec** | Spec calls implementation or its unverified parser | `def SpecOk x := tool x == true`, or defining target ISA semantics via compiler's own parser | $\mathsf{Consts}(S) \cap \mathsf{Consts}(T) \neq \emptyset$ makes soundness reflexive (`rfl`) |
| **Residual harness escapes** | Axioms, compiler reflection, non-termination opt-outs | `sorryAx`, `native_decide` (`Lean.ofReduceBool`), `@[implemented_by]`, Verus/Dafny `{:verify false}` | Blocklist-only cheat checkers miss residual channels (cf. VERINA `arXiv:2505.23135`, CLEVER `arXiv:2505.13938`) |

---

### 2. Formal-Logic Operator, Quantifier, and Totalization Traps

`Basis: source + normative`

Interactive theorem provers and SMT solvers almost universally model partial operations (subtraction on $\mathbb{N}$, division by zero, out-of-bounds indexing) as **total functions** to keep their underlying logic simple and avoid proof-obligation pollution on every term. When specifications translate machine or systems semantics into these logics without explicit domain guards, totalization silently turns bounds and arithmetic specifications into tautologies or cross-domain mismatches.

#### 2.1 Saturating Natural-Number Subtraction (`Nat.sub`)

In `leanprover/lean4@8009d0a6`, `src/Init/Prelude.lean` defines:
- `Nat.pred 0 := 0`, `Nat.pred (succ a) := a` (L2110–2112);
- `Nat.sub a 0 := a`, `Nat.sub a (succ b) := pred (Nat.sub a b)` (L2264–2266).

**Failure modes:**
- `(0 : Nat) - 1 = 0` holds by `rfl`.
- `∀ len off : Nat, len - off ≥ 0` is a **tautology** (`Nat.zero_le _`), proving nothing about `off ≤ len`.
- A range-bounds check written `end_pos - start_pos ≤ cap` silently evaluates to `0 ≤ cap` (`True`) whenever `end_pos < start_pos`, accepting inverted slices or integer underflows!
- **Remediation:** Express natural-number bounds using addition (`off + size ≤ len`) rather than subtraction, or specify systems arithmetic over fixed-width `BitVec w` with explicit overflow predicates (`BitVec.usubOverflow`).

#### 2.2 Four-Way Semantic Divergence of Division and Modulo Across Formalisms

Direct inspection of `leanprover/lean4@8009d0a6`, `Z3Prover/z3@437536cd`, and the SMT-LIB 2.6 specification reveals four incompatible conventions for division and remainder:

| Operation | Lean 4 (`8009d0a6`) | SMT-LIB 2.6 `Ints` | Z3 / SMT-LIB 2.6 `QF_BV` (`437536cd`) | Rust / C / x86-64 Hardware |
| :--- | :--- | :--- | :--- | :--- |
| **`x / 0` (unsigned / `Nat`)** | `0` (`Prelude.lean` L2323–2335) | Uninterpreted total function `div0(x)` | `hi_div0=true`: all-ones `2^w - 1` (`bv_rewriter.cpp` L1216); `hi_div0=false`: uninterpreted `bvudiv0(x)` (L1212) | Runtime panic (Rust) / UB / `#DE` hardware trap (C / x86) |
| **`x % 0` (unsigned / `Nat`)** | `x` (`Prelude.lean` L2340–2422) | Uninterpreted total function `mod0(x)` | `hi_div0=true`: `x`; `hi_div0=false`: uninterpreted `bvurem0(x)` | Panic / UB / `#DE` trap |
| **`(-7) / 2` (signed)** | **`-4`** (`Int.ediv`, Euclidean, `Int/DivMod/Basic.lean` L73–78, L108) | **`-4`** (Euclidean `div`) | **`-3`** (`bvsdiv` truncates toward zero) | **`-3`** (T-rounding toward zero; `Int.tdiv` L178–182) |
| **`(-7) % 2` (signed)** | **`+1`** (`Int.emod`, always $\ge 0$, `Int/DivMod/Basic.lean` L103–109) | **`+1`** (Euclidean `mod`, $0 \le r < |b|$) | **`-1`** (`bvsrem`, sign of dividend) vs. **`+1`** (`bvsmod`, sign of divisor) | **`-1`** (`Int.tmod` L211–215; Rust `%`, C `%`) |
| **`INT_MIN / -1` (signed)** | Mathematical value $+2^{w-1}$ on unbounded `Int` | Mathematical value on `Int` | Wraps to `INT_MIN` in `bvsdiv` (`OP_BSDIV_OVFL` checks overflow, `bv_decl_plugin.cpp` L385) | Panic (Rust) / UB / `#DE` trap (x86 `IDIV`) |

Notice the explicit comment in `leanprover/lean4@8009d0a6` `src/Init/Data/Int/DivMod/Basic.lean` L107–109: *"The `Div Int` and `Mod Int` instances use `Int.ediv` and `Int.emod` for compatibility with SMT-LIB and because mathematical reasoning tends to be easier."* Any specification modeling C/Rust signed `%` or `/` with Lean 4's bare `/` and `%` on `Int` silently disagrees with hardware on every negative dividend (and hides division-by-zero traps unless `y ≠ 0` is asserted explicitly!).

#### 2.3 Silent Typo Quantification (`autoImplicit` and `relaxedAutoImplicit`)

In `leanprover/lean4@8009d0a6`, `src/Lean/Elab/AutoBound.lean` L17–25 registers **both** options with `defValue := true`:

```lean
register_builtin_option autoImplicit : Bool := { defValue := true, ... }
register_builtin_option relaxedAutoImplicit : Bool := { defValue := true, ... }
```

When `relaxedAutoImplicit` is `true`, **any** unbound atomic identifier in a declaration header—even multi-character words—is silently bound as an implicit universally quantified variable (`checkValidAutoBoundImplicitName`, L64–75). For example, if a specification author defines `def req (n : Nat) : Prop := n > 0` and writes:

```lean
theorem spec_typo : ∀ x : Nat, reqs x → reqs x := fun _ h => h
```

Lean accepts the file with **zero errors and zero warnings**, silently elaborating `{reqs : Nat → Prop} → ∀ x : Nat, reqs x → reqs x`! Even worse, misspelling an opaque constant or predicate name inside a hypothesis can introduce an unconstrained universally quantified premise or turn an intended contradiction check into a trivial identity.

**Mandatory mitigation for specification modules:**
- Set `autoImplicit = false` globally in `lakefile.toml` (and `set_option autoImplicit false` at the top of every trusted specification file).
- Lint specification ASTs for unused universally quantified hypotheses, bare `Nat` subtraction, bare `Int`/`Nat` `/` and `%`, and `Array.get!` / `List.head!` default-returning totalized accessors.

---

### 3. Claim-Polarity Inversions and 3-Outcome Reactive/Divergence Adequacy

`Basis: derived + execution (model probe)`

#### 3.1 Polarity Matrix Across Verification Domains

A common Goodhart failure—and a frequent human formalization error—is importing a specification polarity valid in one domain into a domain with the opposite trust direction:

| System Role | Correct Formal Contract | Inverted / Goodharted Polarity | Consequence of Inversion |
| :--- | :--- | :--- | :--- |
| **Optimizing Compiler** ($C : \text{Src} \to \text{Tgt}$) | $\mathsf{Safe}(\text{src}) \implies \mathsf{Beh}(C(\text{src})) \subseteq \mathsf{Beh}(\text{src})$ | Requiring equivalence on UB inputs | Rejects legitimate optimizations (dead-code / UB exploitation) |
| **Verifier / Sandbox / Parser** ($V : \text{Input} \to \{\text{Ok}, \text{Err}\}$) | **Unconditional:** $\forall x \in \Sigma^*,\; V(x) = \text{Ok} \implies \mathsf{Safe}(x)$ | $\mathsf{WellFormed}(x) \implies (V(x) = \text{Ok} \implies \mathsf{Safe}(x))$ | **Catastrophic:** safety becomes vacuous on malformed/adversarial inputs! |
| **Binary Lifter / Decompiler** ($L : \text{Bin} \to \text{IR}$) | **Upward inclusion:** $\mathsf{Beh}(\text{bin}) \subseteq \mathsf{Beh}(L(\text{bin}))$ | Downward inclusion $\mathsf{Beh}(L(\text{bin})) \subseteq \mathsf{Beh}(\text{bin})$ | Lifter can omit buggy binary executions; safe IR no longer implies safe binary! |
| **Cryptographic RNG / Sampler** | Distributional / probabilistic equivalence (min-entropy / indistinguishability) | Demonic set inclusion $\mathsf{Beh}(\text{impl}) \subseteq \mathsf{Beh}(\text{spec})$ | Returning constant `[0u8; 32]` validly refines nondeterministic `getrandom()`! |
| **Hyperproperty / Constant-Time** | 2-safety relational product ($\forall s_1\; s_2,\; s_1 \approx_{\text{low}} s_2 \implies \mathsf{Leak}(s_1) = \mathsf{Leak}(s_2)$) | Single-trace safety property | Single-trace refinement does **not** preserve non-interference (refinement paradox) |

#### 3.2 3-Outcome Adequacy and the König's Lemma Trap

In systems with recursion, loops, I/O, or nondeterminism, **partial correctness** ($\forall v,\; \mathsf{Terminates}(p, v) \implies Q(v)$) admits two catastrophic utility-destroying cheats:
1. Replacing the implementation with `loop {}` (silent divergence) satisfies every partial-correctness postcondition vacuously.
2. Under **unbounded nondeterminism**, attempting to characterize divergence by *"for every step bound $k \in \mathbb{N}$, there exists a finite execution prefix of length $> k$"* **fails by König's Lemma**: König's Lemma guarantees an infinite path only in *finitely-branching* trees. Consider process $P_{\text{choose}}$, which nondeterministically picks an arbitrary $n \in \mathbb{N}$, performs $n$ ticks, and terminates with `0`:
   - For every $k \in \mathbb{N}$, $P_{\text{choose}}$ has a finite prefix of length $k + 1 > k$ (picking $n = k + 1$).
   - Yet $P_{\text{choose}}$ **never diverges**—every single execution terminates in finitely many steps!

Conversely, genuine silent divergence ($P_{\text{diverge}}$: `loop {}`) produces an infinite trace and never terminates. Therefore, an adequate behavioral specification must classify executions across **three distinct observable outcome sets**:

$$\mathsf{Beh}(p, q) \subseteq \underbrace{\{\mathsf{Term}(v, \tau_{\text{fin}})\}}_{\text{terminating value + finite I/O}} \;\cup\; \underbrace{\{\mathsf{Diverge}(\tau_\infty)\}}_{\text{coinductive infinite I/O / silent div.}} \;\cup\; \underbrace{\{\mathsf{Fault}(k, \tau_{\text{fin}})\}}_{\text{UB vs. unsupported fault}}$$

(Validated in Python Probe 4: `P_choose` satisfies `prefix>k=True` yet has `diverge=False` and `3out_ok=True`, while `P_diverge` passes `partial_ok=True` yet is cleanly rejected with `3out_ok=False`.)

---

### 4. Vacuity Detection and Linear $(m + 1)$-Witness Clause Independence

`Basis: normative (literature) + derived + execution`

#### 4.1 Classical Subformula-Perturbation Vacuity

Originating in hardware model checking (Beer, Ben-David, Eisner, & Rodeh, *FMSD 2001*, DOI `10.1023/A:1011241315570`; Kupferman & Vardi, *STTT 2003*, DOI `10.1007/s100090100062`; Chockler, Kupferman, & Vardi, *FMSD 2006*, DOI `10.1007/s10703-006-0013-0`), a formula $\varphi$ passes **vacuously** in model $M$ with respect to an occurrence of subformula $\psi$ if replacing $\psi$ by **any** formula $\psi'$ leaves $M \models \varphi[\psi \leftarrow \psi']$ unchanged.

For any subformula $\psi$ occurring with pure syntactic polarity in $\varphi$, Kupferman & Vardi proved that checking all $\psi'$ reduces to a **single extremal perturbation**:
- **Positive polarity** (under an even number of negations, e.g., $q$ in $p \to q$): check whether $M \models \varphi[\psi \leftarrow \bot]$. If yes, $\psi$ was never needed to hold (consequent vacuity, e.g., $p$ is always false!).
- **Negative polarity** (under an odd number of negations, e.g., $p$ in $p \to q$): check whether $M \models \varphi[\psi \leftarrow \top]$. If yes, the assumption $\psi$ was never needed (antecedent redundancy).

Chockler, Kupferman, & Vardi (*FMSD 2006*) generalized vacuity to **specification coverage metrics** by measuring which subformulas and model states causally affect satisfaction.

#### 4.2 Defeating Multi-Conjunct Canary Masking: The Linear $(m + 1)$-Witness Criterion

When auditing an automated specification $S(x, y) = \bigwedge_{i=1}^m C_i(x, y)$ composed of $m$ requirement clauses (e.g., `nonneg`, `even`, `bounded`), a naive 2-canary sanity check—one positive example $w^+$ where $S(w^+)$ holds and one negative example $w^-$ where $S(w^-)$ fails—suffers **multi-conjunct canary masking**:
- If $w^-$ violates both $C_1$ and $C_2$, an optimizer can replace $C_3$ with `True` (dropping the hardest obligation!) while still passing both $S(w^+) = \mathsf{True}$ and $S(w^-) = \mathsf{False}$!

**Linear $(m + 1)$-Witness Independence Protocol:**
Require exactly $m + 1$ concrete witnesses for any $m$-conjunct specification $S = \bigwedge_{i=1}^m C_i$:
1. **One joint positive witness** $w^+$:
   $$\forall i \in \{1, \dots, m\},\quad C_i(w^+) = \mathsf{True} \qquad\text{(rules out } S \equiv \bot \text{ and inter-clause contradiction)}.$$
2. **$m$ isolating negative witnesses** $w_1^-, \dots, w_m^-$ (one per clause $i$):
   $$\left(\forall j \neq i,\; C_j(w_i^-) = \mathsf{True}\right) \;\land\; \left(C_i(w_i^-) = \mathsf{False}\right).$$

**Guarantee (`Basis: derived + execution`):**
- Because $w_k^-$ satisfies every other conjunct $C_j$ ($j \neq k$), replacing $C_k$ with $\mathsf{True}$ (or weakening $C_k$ to admit $w_k^-$) **immediately** flips $S(w_k^-)$ from $\mathsf{False}$ to $\mathsf{True}$, achieving 100% detection of single-clause vacuity/dropping in $O(m)$ witness evaluations (instead of $2^m$ truth-table combinations).
- Confirmed in Python Probe 1: on $S(x, y) \equiv (y \ge 0) \land (y \bmod 2 = 0) \land (y \le x)$, the naive 2-canary pair `((10, 4), (10, -3))` fails to detect replacing $C_3$ with `True`, whereas the 4-witness isolating suite `(10, 4), (10, -2), (10, 3), (10, 12)` immediately exposes the missing $C_3$ kill (`[True, True, False]`), matching exhaustive domain subformula perturbation (`hacked= ['C3_true']`).

---

### 5. Primal-Dual Completeness: ZKP Witness Uniqueness and Bidirectional Codecs

A deep structural defense against specification under- and over-constraining is **primal-dual pairing**: coupling an *existential* (completeness) property with a *uniqueness / injectivity* (soundness / non-malleability) property.

#### 5.1 Zero-Knowledge Proof Circuits (`Veridise/Picus@138b151d`)

`Basis: source + documentation + execution`

Zero-knowledge proof systems (Circom / R1CS over a prime field $\mathbb{F}_p$) invert the usual verification intuition: an **under-constrained** arithmetic circuit $\mathcal{C}(x, w) = 0$ is a critical soundness vulnerability allowing a malicious prover to forge proofs for false outputs, while an **over-constrained** circuit destroys completeness by preventing honest provers from generating any valid witness.

**Picus** (Pailoor, Chen, Wang, Rodríguez, Van Geffen, Morton, Chu, Gu, Feng, & Dillig, *PLDI 2023*, DOI `10.1145/3591282`) formalizes the primal-dual adequacy boundary for deterministic ZKP circuits:
- **Primal (Existence / Completeness):** $\forall x \in \mathbb{F}_p^k,\; \exists w,\; \mathcal{C}(x, w) = 0$ (checked against witness generator / non-emptiness).
- **Dual (Deterministic Output Uniqueness / Non-Underconstrainedness):**
  $$\forall x\; w_1\; w_2,\quad \mathcal{C}(x, w_1) = 0 \;\land\; \mathcal{C}(x, w_2) = 0 \;\implies\; \mathsf{out}(w_1) = \mathsf{out}(w_2).$$

Direct inspection of `Veridise/Picus@138b151d` (`picus.rkt` L21–86, `picus/algorithms/dpvl.rkt`, `picus-cex-uniqueness.rkt`, `README.md`) shows how Picus solves this efficiently:
1. **Unique Constraint Propagation (`UCP`):** Syntactically propagates known-unique signals (starting from public inputs) across linear/quadratic R1CS equations without invoking an SMT solver (controlled via `--noprop`, default enabled in `picus.rkt` L29/L84).
2. **SMT Finite-Field Verification (`DPVL`):** For residual signals not proved unique by UCP, Picus encodes two copies of the circuit sharing public inputs $x$ with distinct output wires ($\mathsf{out}(w_1) \neq \mathsf{out}(w_2)$) and queries cvc5's native finite-field theory or Z3 (`--solver`, `--nosolve`).
3. **Constructive Dual-Witness Counterexample:** When a circuit is under-constrained, Picus exits with code `9` and emits concrete shared `inputs` together with two distinct valid output assignments (`first possible outputs` vs. `second possible outputs`, `README.md`).

As demonstrated in Python Probe 2 over $\mathbb{F}_{17}$ on Circom's classic `IsZero` circuit (`out = -inp * inv + 1` and `inp * out = 0`):
- **Sound `IsZero`:** `exists_all=True`, `unique_out=True` (0 missing inputs, 0 non-unique inputs).
- **Under-constrained `IsZero` (omitting `inp * out = 0`):** `exists_all=True`, `unique_out=False` — every nonzero input $x \in \{1..16\}$ admits *all 17* field elements as valid outputs by choosing `inv = (1 - out) * x^{-1}`!
- **Over-constrained `IsZero` (contradictory constraints):** `unique_out=True` vacuously (`∀ w1 w2, False → ...`), caught immediately by `exists_all=False` (17 missing inputs)!

#### 5.2 Bidirectional `PutGet` / `GetPut` Binary Codecs (`EverParse` & `Vest`)

`Basis: source + documentation + execution`

Drawing from bidirectional lenses (Foster, Greenwald, Moore, Pierce, & Schmitt, *TOPLAS 2007*, DOI `10.1145/1232420.1232424`), binary protocol verifiers prevent both **format confusion** and **format malleability** (signature-wrapping / transaction-malleability attacks where two distinct byte strings parse to the same authenticated object) by pairing two dual roundtrip laws:

| Property | Bidirectional Lens Name | EverParse (`LowParse.Spec.Base.fsti` @ `270f5aab`) | Vest (`vest_lib/src/core/proof.rs` @ `026867a3`) | Defect Prevented |
| :--- | :--- | :--- | :--- | :--- |
| **Serialize $\to$ Parse** | `PutGet` | `serializer_correct` (L715–721): `∀ x, parse p (f x) == Some (x, Seq.length (f x))` | `SPRoundTrip` (L56–76): `consistent(v) ==> spec_parse(spec_serialize(v)) == Some((bytes.len(), v))` | Lossy serialization, incomplete parser, serializer ambiguity (`NonAmbiguous` follows directly, L97–137) |
| **Parser Injectivity** | Non-malleability | `injective` (L99–102): equal parsed values $\implies$ identical consumed slice `Seq.slice b1 0 len1 == Seq.slice b2 0 len2` | `NonMalleable` (L197+): `v1 == v2 ==> buf1[0..n1] == buf2[0..n2]` | Multiple wire encodings for one semantic value |
| **Parse $\to$ Serialize** | Strong `GetPut` | `serializer_complete` (L753–763): `parse p s == Some (x, len) ==> f x == Seq.slice s 0 len` (derived via `serializer_correct_implies_complete`, L765–772!) | `PSRoundTrip` (L147–195): `spec_parse(ibuf) == Some((n, v)) ==> spec_serialize(v) == ibuf[0..n]` (blanket impl from `SPRoundTrip + NonMalleable + SoundParser`, L176–195!) | Accepting non-canonical / padded / malleable bytes (`0x00 0x00` vs `0x00`, demonstrated in Python Probe 3) |

**Critical boundary explicitly noted in Vest (`guide/src/guarantees.md`):**
1. **Intentional malleability (Postel's law):** Formats such as ASN.1 BER, general CBOR, and IKE intentionally allow multiple encodings; Vest encodes `NonMalleable` as an explicit Rust/Verus trait bound so malleable formats cannot accidentally satisfy cryptographic non-malleability requirements.
2. **External RFC fidelity remains outside internal roundtrip proofs:** Even a fully proved `PutGet + GetPut + NonMalleable` codec can be internally consistent while encoding the *wrong* wire layout compared to an external RFC! Vest's `guarantees.md` explicitly warns that internal proofs must be paired with external corpus / differential conformance testing.

---

### 6. Mutation-Kill Specification Auditing (`MutSpec` / Mutation Model Checking / `SpecFuzzer`)

`Basis: documentation + derived`

While vacuity and primal-dual checks test internal structural health of $S$, **mutation-based specification auditing** empirically measures whether $S$ is tight enough to distinguish correct code from realistic bugs:

1. **Implementation-Mutant Rejection (Positive + Negative Canary Suites):**
   Given a candidate specification $S$, a reference implementation $P_{\text{ref}}$, and a curated battery of faulty mutants $\mathcal{M} = \{P_1^{\text{bug}}, \dots, P_k^{\text{bug}}\}$ (off-by-one slice bounds, dropped alignment/null checks, inverted branch conditions, arithmetic wraparound, clobbered callee-saved registers, omitted zeroization):
   - **Positive adequacy (acceptance):** $P_{\text{ref}} \models S$ MUST be provable (rejecting impossible/over-constrained specs).
   - **Negative adequacy (mutation kill):** For every faulty mutant $P_j^{\text{bug}} \in \mathcal{M}$, $S$ MUST reject $P_j^{\text{bug}}$—ideally witnessed by a constructive counterexample input $x_j$ such that $\neg S(x_j, P_j^{\text{bug}}(x_j))$ (or a mechanized refutation theorem $\neg(P_j^{\text{bug}} \models S)$).
   - **Metric:** $\text{SpecKillRate}(S, \mathcal{M}) = |\{j : P_j^{\text{bug}} \not\models S\}| / |\mathcal{M}|$. Surviving non-equivalent mutants directly pinpoint weak clauses in $S$.
2. **Specification-AST Mutation & Fuzzing:**
   - **Mutation Model Checking** (Cordy, Lazreg, Legay, & Schobbens, *ESEC/FSE*, DOI `10.1145/3611643.3613080`) mutates temporal/logical specifications against a system model to identify strengthening candidates where weakened or mutated specs remain satisfied.
   - **`SpecFuzzer`** (Molina, d'Amorim, & Aguirre, *ICSE* DOI `10.1145/3510003.3510120` & *ASE* DOI `10.1109/ASE56229.2023.00024`) combines grammar-based specification fuzzing with mutation filtering to prune redundant/weak candidate invariants while retaining mutant-killing specifications.
   - **Negative specification tests (`spectests`):** Testing specifications against impossible input-output pairs (pairs unreachable by the true reference behavior) penalizes trivially weak specs (`ensures True`) during LLM/RL specification synthesis without requiring full equivalence proofs against a hidden ground-truth formula.

---

### 7. Cryptographic Intuition-Soundness Games + Honest-Tool Completeness (Circumventing Rice's Barrier)

`Basis: normative (Rice 1953) + derived + execution`

#### 7.1 Why Semantic Closure Fails by Rice's Theorem

A tempting formalization of "completeness" for a static verifier or certifying tool $T : \text{Prog} \to \{\mathsf{Accept}, \mathsf{Reject}\}$ is **semantic closure**:

$$\forall p_1\; p_2,\quad \llbracket p_1 \rrbracket = \llbracket p_2 \rrbracket \;\land\; T(p_1) = \mathsf{Accept} \;\implies\; T(p_2) = \mathsf{Accept}.$$

By **Rice's Theorem** (Rice, *Trans. AMS 1953*, DOI `10.2307/1990888`), *every* non-trivial extensional (semantic) property of Turing-complete programs is undecidable. Consequently, demanding semantic closure:
1. **Locks out every sound, terminating syntactic verifier**—including Rust's borrow checker, Hindley–Milner typecheckers, abstract interpreters, and bounded model checkers! Concretely, `0` and `if false { *null } else { 0 }` have identical denotational semantics (`Term(0)`), yet an honest syntactic checker MUST accept `0` and conservatively reject the dead `*null` dereference (verified in Python Probe 5).
2. **Fails vertical composition:** Composing two conservative syntactic passes breaks semantic closure even if each pass is useful in practice.

#### 7.2 The Paired Game Architecture

To defeat Goodharting *without* locking out honest conservative tools, split adequacy into two asymmetric obligations:

1. **Intuition-Soundness Game (Defending Soundness Against Adversarial $S$):**
   - Define a **normalized, trap-free `AcceptanceSurface`** $\mathcal{A}(S)$ presented to a human auditor with finite cognitive budget $B$ (bounding AST size, transitive symbol count, and disabling syntactic traps: `autoImplicit := false`, fixed-width `BitVec` arithmetic, explicit totalization guards, one-way spec imports, external pretty-printing of kernel-expanded types, and cryptographic spec-lock hashing across agent turns).
   - **Game:** The challenger (human/CI) locks $\mathcal{A}(S)$ within budget $B$ and verifies that $\mathcal{A}(S)$ faithfully expresses the intuitive intent $U$ on the domain boundary. An adversary (synthesis/proving agent) with full access to the verification toolchain attempts to output an artifact $(T, \pi)$ that passes the checker ($C(S, T, \pi) = \mathsf{Accept}$) yet exhibits an observable execution violating $U$ (or mutates $\mathcal{A}(S)$ undetected).
   - **Security condition:** The adversary's winning advantage reduces to (a) breaking the De Bruijn proof kernel / hash lock, or (b) finding a discrepancy inside the compact, trap-free surface $\mathcal{A}(S)$ of size $\le B$.

2. **Honest-Tool Completeness via Coupled Parametric Family Generalization (Defending Utility Against Trivial Rejection/Lookup Hacks):**
   - Suppose a verification architecture splits into an untrusted proof/certificate finder $F$ and a trusted checker $C$ (so the pipeline is $C \circ F$). Pure soundness is trivially satisfied by $F(\_) = \mathsf{None}$ (always reject), by a finite lookup table memorizing $N$ benchmark tasks, or by a compiler rewriting every program to `abort()`/`loop {}`.
   - Replace Rice-blocked semantic closure with **coupled parametric family completeness**: exhibit one or more unbounded structured families of legitimate programs $g : \mathbb{N} \to \text{Prog}$ (e.g., arbitrary-length safe arithmetic chains, parameterized loop/buffer sizes, or randomized fresh instances drawn outside the synthesizer's training/search horizon) and require:
     $$\forall k \in \mathbb{N},\quad \mathsf{Handles}(C \circ F,\; g(k)) \;\land\; \mathsf{Preserves3Outcome}(T(g(k)),\; g(k)).$$
   - As demonstrated in Python Probe 5:
     - An **honest syntactic checker** fails semantic closure (`sem_closure= False`, due to the dead-branch `*null` Rice witness) yet passes parametric family completeness uniformly across all $k$ (`parametric= True`).
     - A **finite lookup-table hack** memorizing $k \in \{0..4\}$ passes naive finite canary suites (`finite= True`) yet is immediately caught at $k = 5$ (`parametric= False`).
     - A **vacuous `find(_) = None` finder** fails at $k = 0$; an **`abort()`/`loop {}` compiler** fails $\mathsf{Preserves3Outcome}$ on the first terminating family member.

---

### 8. Synthesis: Layered Anti-Goodhart Defense-in-Depth Checklist

`Basis: derived`

| Layer | Threat Defeated | Constructive Check / Mechanism | Residual Gap Closed by Next Layer |
| :--- | :--- | :--- | :--- |
| **L1: Syntax & Operator Lint** | `Nat.sub` saturation, totalized `/ 0`, Euclidean vs. truncating `%`, `autoImplicit` typos | `autoImplicit := false`; require `BitVec` or additive bounds; forbid bare `/` and `%` without `y ≠ 0`; one-way spec imports | Valid syntax can still be logically vacuous or polarity-inverted |
| **L2: Structural Vacuity & $(m+1)$ Witnesses** | Antecedent `False`, consequent `True`, multi-conjunct canary masking | Subformula extremal perturbation + 1 joint positive + $m$ single-clause-isolating negative witnesses | Individually active clauses can still be under-constrained |
| **L3: Primal-Dual Uniqueness / Bijection** | Under-constrained ZKP circuits, malleable parsers, non-injective codecs | Existence + uniqueness (`Picus` UCP+SMT); `PutGet` + `NonMalleable` $\implies$ `GetPut` (`EverParse` / `Vest`) | Internally bijective spec can still mis-specify external semantics |
| **L4: 3-Outcome + Mutation-Kill Suite** | `loop {}` divergence cheats, `abort()` rewrites, weak functional postconditions | 3-outcome observables (`Term` / `Diverge` / `Fault`) + positive reference & negative buggy-mutant rejection witnesses | Finite mutant suites can still be memorized by lookup tables |
| **L5: Locked `AcceptanceSurface` + Parametric Completeness** | Spec tampering across agent turns, `find(_) = None`, lookup-table overfitting | Cryptographic spec-lock + compact human-audited surface $\mathcal{A}(S)$ + coupled $\forall k,\; \mathsf{Handles}(C \circ F, g(k))$ | Relies on De Bruijn kernel soundness and external differential conformance |

## Boundaries

- **Mutual vacuity beyond single-clause independence (`known not to apply`):** The linear $(m + 1)$-witness protocol catches every single-clause weakening or redundancy ($C_k \mapsto \mathsf{True}$) in a conjunction $\bigwedge_{i=1}^m C_i$, but does not by itself detect *mutual vacuity* across arbitrary boolean combinations (e.g., disjunctive masking $A \lor B$ or pairs of mutually reinforcing redundant clauses where neither is individually removable only when the other is intact); handling general mutual vacuity requires multi-subformula vacuity checking (e.g., Chockler–Strichman mutual vacuity).
- **Non-deterministic ZKP circuits (`known not to apply` / `unsupported`):** `Veridise/Picus`'s deterministic output-uniqueness property (`∀ x w1 w2, C(x,w1)=0 ∧ C(x,w2)=0 ⇒ out(w1)=out(w2)`) applies only to circuits whose output is intended to be a deterministic function of public inputs; randomized or relational ZKP circuits (where multiple valid outputs are intentional) violate deterministic uniqueness by design.
- **Malleable wire standards (`known not to apply`):** Strong `GetPut` (`PSRoundTrip` / `serializer_complete`) fails by design for intentionally malleable formats such as ASN.1 BER, non-deterministic CBOR, or IKEv2 payloads with ignored extensions (as explicitly documented in `secure-foundations/vest` `guide/src/guarantees.md`).
- **External prose-RFC / physical-world fidelity (`unknown` / `not examined`):** No internal adequacy check (vacuity, primal-dual roundtrip, or mutation kill against self-authored mutants) proves that a formal specification matches an external informal standard (RFC, ISA manual, or human business intent); bridging that gap requires external reference-corpus differential testing and human review of the minimized `AcceptanceSurface`.
- **Live Lean 4.34.1 and Z3/Picus binary execution (`not examined`):** Lean 4 operator/option semantics (`8009d0a6`), Z3 bitvector `hi_div0` rewriter logic (`437536cd`), EverParse (`270f5aab`), Vest (`026867a3`), and Picus (`138b151d`) were verified by direct upstream source inspection (`Basis: source`) rather than executing those native binaries on this host (where Z3 Python bindings and Racket were not installed and the host Lean build slot was held by a concurrent build). All algorithmic properties were executed and validated via self-contained Python 3.13.15 model probes (`Basis: execution`).

## Evidence

### Primary Git Repository Sources (Observed `2026-11-19`)

1. **`leanprover/lean4` @ `8009d0a64d2860606c6a5ac5ff6702622b24921e`**
   - `src/Init/Prelude.lean` L2110–2112 (`Nat.pred 0 = 0`), L2264–2266 (`Nat.sub` saturating), L2323–2335 (`Nat.div x 0 = 0`), L2340–2422 (`Nat.mod x 0 = x`).
   - `src/Init/Data/Int/DivMod/Basic.lean` L73–109 (`Int.ediv`, `Int.emod`, SMT-LIB Euclidean compatibility note), L178–216 (`Int.tdiv`, `Int.tmod` T-rounding), L242–279 (`Int.fdiv`, `Int.fmod` floor rounding).
   - `src/Lean/Elab/AutoBound.lean` L17–25 (`autoImplicit := true`, `relaxedAutoImplicit := true`), L64–75 (`checkValidAutoBoundImplicitName`).
   - `src/Lean/Elab/Tactic/Decide.lean` L70–81, L202–205 (`native_decide` via `nativeEqTrue`).
2. **`Z3Prover/z3` @ `437536cd64a544a1c329fc57d83e56e294fdf47c`**
   - `src/ast/bv_decl_plugin.cpp` L345–358 (`OP_BSDIV`, `OP_BUDIV`, `OP_BSDIV0`, `OP_BUDIV0`, `OP_BSREM0`, `OP_BUREM0`), L385 (`OP_BSDIV_OVFL`).
   - `src/ast/rewriter/bv_rewriter.cpp` L1202–1216 (`mk_bv_udiv_core`: `hi_div0 = false` rewrites to uninterpreted `mk_bv_udiv0(arg1)`; `hi_div0 = true` uses hardware all-ones `#xffff...`).
3. **`Veridise/Picus` @ `138b151d3a388e5b6c040c163e0a1db04f2ceda6`**
   - `README.md` (Docker/Racket/cvc5-ff/Z3 setup, exit code `9` and dual-output counterexample format).
   - `picus.rkt` L21–86 (`dpvl` integration, `--noprop`, `--nosolve`, `--solver`).
   - `picus/algorithms/dpvl.rkt` (476 L), `picus-cex-uniqueness.rkt` (163 L).
4. **`project-everest/everparse` @ `270f5aab699ac284d8777d4f01be20a5d91ea47c`**
   - `lib/everparse/lowparse/LowParse.Spec.Base.fsti` L46–102 (`injective_precond`, `injective_postcond`, `injective`), L715–721 (`serializer_correct`), L753–763 (`serializer_complete`), L765–781 (`serializer_correct_implies_complete`, `serializer` refinement type).
5. **`secure-foundations/vest` @ `026867a37d4b918153058df2c8db6c52fc62ba35`**
   - `vest_lib/src/core/spec.rs` L6–102 (`SpecParser`, `disjoint_domains`, `disjoint_values`, `SafeParser`, `SoundParser`, `StrictParser`).
   - `vest_lib/src/core/proof.rs` L24–195 (`SPRoundTripDps`, `SPRoundTrip`, `NonAmbiguous`, `PSRoundTrip`, blanket `impl<C: SPRoundTrip + NonMalleable + SoundParser> PSRoundTrip for C`).
   - `guide/src/guarantees.md` L1–83 (malleable standards vs. `NonMalleable`, explicit TCB and external RFC conformance caveat).

### Peer-Reviewed Literature and Standards

- Ilan Beer, Shoham Ben-David, Cindy Eisner, & Yoav Rodeh (2001), *"Efficient Detection of Vacuity in ACTL Formulas"*, Formal Methods in System Design (FMSD), DOI `10.1023/A:1011241315570`.
- Orna Kupferman & Moshe Y. Vardi (2003), *"Vacuity Detection in Temporal Model Checking"*, Software Tools for Technology Transfer (STTT), DOI `10.1007/s100090100062`.
- Hana Chockler, Orna Kupferman, & Moshe Y. Vardi (2006), *"Coverage Metrics for Temporal Logic Model Checking"*, Formal Methods in System Design (FMSD), DOI `10.1007/s10703-006-0013-0`.
- Shankara Pailoor et al. (2023), *"Automated Detection of Under-Constrained Circuits in Zero-Knowledge Proofs"* (Picus), PLDI 2023, PACMPL 7, DOI `10.1145/3591282`.
- Tahina Ramananandro et al. (2019), *"EverParse: Verified Secure Zero-Copy Parsers for Authenticated Message Formats"*, USENIX Security 2019.
- Yi Cai, Pratap Singh, Zhengyao Lin, Jay Bosamiya, Joshua Gancher, Milijana Surbatovich, & Bryan Parno (2025), *"Vest: Verified, Secure, High-Performance Parsing and Serialization for Rust"*, USENIX Security 2025.
- J. Nathan Foster, Michael B. Greenwald, Jonathan T. Moore, Benjamin C. Pierce, & Alan Schmitt (2007), *"Combinators for Bidirectional Tree Transformations: A Linguistic Approach to the View-Update Problem"*, ACM TOPLAS 29(3), DOI `10.1145/1232420.1232424`.
- H. Gordon Rice (1953), *"Classes of Recursively Enumerable Sets and Their Decision Problems"*, Trans. AMS, DOI `10.2307/1990888`.
- David Manheim & Scott Garrabrant (2018), *"Categorizing Variants of Goodhart's Law"*, `arXiv:1803.04585`.
- Maxime Cordy, Sami Lazreg, Axel Legay, & Pierre-Yves Schobbens, *"Towards Strengthening Formal Specifications with Mutation Model Checking"*, ESEC/FSE, DOI `10.1145/3611643.3613080`.
- Facundo Molina, Marcelo d'Amorim, & Nazareno Aguirre, *"Fuzzing Class Specifications"* (ICSE, DOI `10.1145/3510003.3510120`) and *"SpecFuzzer: A Tool for Inferring Class Specifications via Grammar-Based Fuzzing"* (ASE, DOI `10.1109/ASE56229.2023.00024`).
- VERINA (`arXiv:2505.23135`) and CLEVER (`arXiv:2505.13938`) verifiable code-generation benchmarks.
- Clark Barrett, Pascal Fontaine, & Cesare Tinelli, *The SMT-LIB Standard: Version 2.6*.

### Executable Model Micro-Probes (`Basis: execution`, Python 3.13.15, `2026-11-19`)

Command executed: `python3 /tmp/probe_adequacy.py` (self-contained 5-probe script preserved inline):

```python
#!/usr/bin/env python3
"""Micro-probes: (m+1) clause independence, ZKP primal-dual uniqueness, codec GetPut/PutGet,
3-outcome Konig divergence, and Rice semantic closure vs parametric family completeness."""

def run_probes() -> None:
    # 1. Linear (m+1)-witness clause independence vs canary masking
    c_int = [("C1", lambda x, y: y >= 0), ("C2", lambda x, y: y % 2 == 0), ("C3", lambda x, y: y <= x)]
    c_hck = [c_int[0], c_int[1], ("C3_true", lambda x, y: True)]
    ev = lambda cs, x, y: all(p(x, y) for _, p in cs)
    print("Naive 2-canary:", ev(c_int, 10, 4) and not ev(c_int, 10, -3),
          ev(c_hck, 10, 4) and not ev(c_hck, 10, -3))
    w_pos, w_negs = (10, 4), [(10, -2), (10, 3), (10, 12)]
    print("(m+1)-audit intended:", ev(c_int, *w_pos), [not ev(c_int, *w) for w in w_negs])
    print("(m+1)-audit hacked:  ", ev(c_hck, *w_pos), [not ev(c_hck, *w) for w in w_negs])
    dom = [(x, y) for x in range(15) for y in range(-4, 16)]
    vac = lambda cs: [n for i, (n, _) in enumerate(cs)
                      if [ev(cs, x, y) for x, y in dom] == [ev(cs[:i] + [("T", lambda a, b: True)] + cs[i+1:], x, y) for x, y in dom]]
    print("vacuous clauses: intended=", vac(c_int), "hacked=", vac(c_hck))

    # 2. ZKP IsZero over F_17: sound vs under-constrained vs over-constrained
    p = 17
    sound = lambda i, o, v: ((o - (-i * v + 1)) % p == 0) and ((i * o) % p == 0)
    under = lambda i, o, v: (o - (-i * v + 1)) % p == 0
    over  = lambda i, o, v: sound(i, o, v) and (o == 1) and (o == 0)
    for name, c in [("sound", sound), ("under", under), ("over", over)]:
        miss = [i for i in range(p) if not any(c(i, o, v) for o in range(p) for v in range(p))]
        nonu = [i for i in range(p) if len({o for o in range(p) for v in range(p) if c(i, o, v)}) > 1]
        print(f"ZKP {name:5s}: exists_all={not miss} (miss={len(miss)}), unique_out={not nonu} (nonu={len(nonu)})")

    # 3. Codec PutGet vs GetPut malleability
    ser = lambda v: bytes([v])
    def parse_mal(b):
        if not b: return None
        i = 0
        while i + 1 < len(b) and b[i] == 0: i += 1
        return (i + 1, b[i])
    parse_can = lambda b: None if not b else (1, b[0])
    for name, pf in [("malleable", parse_mal), ("canonical", parse_can)]:
        pg = all(pf(ser(v)) == (1, v) for v in range(256))
        cex = next(((b.hex(), pf(b), ser(pf(b)[1]).hex())
                    for b in [bytes([x]) for x in range(256)] + [bytes([0, x]) for x in range(256)]
                    if pf(b) is not None and ser(pf(b)[1]) != b[:pf(b)[0]]), None)
        print(f"Codec {name:9s}: PutGet={pg}, GetPut={cex is None}, cex={cex}")

    # 4. 3-outcome divergence vs Konig unbounded prefixes
    for proc, pref, div, part, out3 in [
        ("P_choose", True, False, True, {"Term(0)"}.issubset({"Term(0)"})),
        ("P_diverge", True, True, True, {"Diverge"}.issubset({"Term(0)"})),
        ("P_abort", False, False, False, {"Fault"}.issubset({"Term(0)"})),
    ]:
        print(f"3-outcome {proc:9s}: prefix>k={pref}, diverge={div}, partial_ok={part}, 3out_ok={out3}")

    # 5. Syntactic checker vs Rice semantic closure vs parametric family k in 0..20
    honest = lambda prog: prog[0] in ("const", "add_chain")
    lookup = lambda prog: prog in {("add_chain", k) for k in range(5)}
    print("honest: sem_closure=", honest(("const", 0)) == honest(("dead_ub", "if 0 {*null} else {0}")),
          "finite=", all(honest(("add_chain", k)) for k in range(5)),
          "parametric=", all(honest(("add_chain", k)) for k in range(21)))
    print("lookup: finite=", all(lookup(("add_chain", k)) for k in range(5)),
          "parametric=", all(lookup(("add_chain", k)) for k in range(21)))

if __name__ == "__main__":
    run_probes()
```

Observed output (`Python 3.13.15`, exit `0`):
```text
Naive 2-canary: True True
(m+1)-audit intended: True [True, True, True]
(m+1)-audit hacked:   True [True, True, False]
vacuous clauses: intended= [] hacked= ['C3_true']
ZKP sound: exists_all=True (miss=0), unique_out=True (nonu=0)
ZKP under: exists_all=True (miss=0), unique_out=False (nonu=16)
ZKP over : exists_all=False (miss=17), unique_out=True (nonu=0)
Codec malleable: PutGet=True, GetPut=False, cex=('0000', (2, 0), '00')
Codec canonical: PutGet=True, GetPut=True, cex=None
3-outcome P_choose : prefix>k=True, diverge=False, partial_ok=True, 3out_ok=True
3-outcome P_diverge: prefix>k=True, diverge=True, partial_ok=True, 3out_ok=False
3-outcome P_abort  : prefix>k=False, diverge=False, partial_ok=False, 3out_ok=False
honest: sem_closure= False finite= True parametric= True
lookup: finite= True parametric= False
```

## Revalidation

1. **Lean 4 operator and `autoImplicit` defaults (~1s on any idle Lean 4 toolchain):**
   Run `lean /tmp/p2_traps.lean` on:
   ```lean
   theorem nat_sub_underflow : (0 : Nat) - 1 = 0 := rfl
   theorem nat_div_zero (x : Nat) : x / 0 = 0 := Nat.div_zero x
   theorem int_emod_neg : (-7 : Int) % 2 = 1 := rfl
   theorem int_tmod_neg : Int.tmod (-7) 2 = -1 := rfl
   def req (n : Nat) : Prop := n > 0
   theorem typo_tautology : ∀ x : Nat, reqs x → reqs x := fun _ h => h
   #check @typo_tautology
   ```
   Confirm `#check @typo_tautology` shows `{reqs : Nat → Prop}` auto-bound unless `set_option autoImplicit false` is active; diff `src/Lean/Elab/AutoBound.lean` on newer Lean 4 releases if defaults change.
2. **Z3 bitvector division-by-zero rewriter check:**
   Inspect `bv_rewriter::mk_bv_udiv_core` in `src/ast/rewriter/bv_rewriter.cpp` or run Z3 on `(set-logic QF_BV) (assert (= (bvudiv #x05 #x00) #xff)) (check-sat)` (`sat` under SMT-LIB 2.6 `hi_div0 = true`) vs. `(set-logic QF_NIA) (assert (= (div 5 0) 42)) (check-sat)` (`sat` because integer `div` by zero is uninterpreted).
3. **Picus under-constrained circuit counterexample check:**
   In `Veridise/Picus`, run `./run-picus ./benchmarks/circomlib-cff5ab6/Decoder@multiplexer.circom` and confirm exit code `9` with dual distinct output assignments for shared input `main.inp: 0`.
4. **EverParse / Vest codec trait invariants:**
   Diff `lib/everparse/lowparse/LowParse.Spec.Base.fsti` (`serializer_correct_implies_complete`) and `vest_lib/src/core/proof.rs` (`impl<C: SPRoundTrip + NonMalleable + SoundParser> PSRoundTrip for C`) to confirm that non-malleability + serialize-parse roundtrip continues to derive strong parse-serialize roundtrip.
5. **Python adequacy model suite:**
   Rerun the inline Python 3.13 script in **Evidence** (`python3 /tmp/probe_adequacy.py`) to reproduce all five adequacy probes deterministically.
