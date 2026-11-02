<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Tractability, Decidability, Gödel–Tarski–Löb Incompleteness, and the Formalization Gap in Anti-Goodhart Verification

## Summary

Formalizing what it means for a program specification and verification tool to
be non-pathological, non-vacuous, and aligned with human intuition confronts
four foundational impossibility boundaries in mathematical logic, computability
theory, and the philosophy of computation:

1. **The Tarski–Gödel–Löb Meta-Language Boundary (Why Axiom Hygiene Cannot Be an
   Object-Language `Prop`):**
   While structural properties of verification units and behaviors—such as zero
   waivers (`u.waived = []`), unique obligation identifiers (`NoDupIds`),
   constructor-gated obligations (`private mk ::` on `Obligation`),
   domain-locked non-vacuity (`Language.dom`), and paired negative canaries
   (`VerifiedSpineWithCanaries`)—can be enforced inside Lean's object-level type
   theory (`Trusted/Refinement.lean`), **meta-theoretic soundness of the proof
   environment itself** (verifying that a proof term did not invoke `sorryAx`,
   `Classical.choice`, `Lean.ofReduceBool`, `@[implemented_by]`, or `unsafe`)
   cannot be enforced by conjoining an object-level proposition
   `InternalNoSorryProp : Prop` onto `StrictUnitTheorem u`. By the Principle of
   Explosion (`sorryAx : ∀ {α : Sort u}, α`), Tarski's Undefinability Theorem
   (Tarski 1933/1935), Gödel's Second Incompleteness Theorem (Gödel 1931), and
   Löb's Theorem (Löb 1955), any environment containing `sorryAx` proves
   `StrictUnitTheorem u ∧ InternalNoSorryProp` in one step
   (`internal_self_certification_explodes`,
   `godel_second_incompleteness_from_lob`). Auditing the axiom footprint and
   environment integrity therefore *must* reside in the Tarskian meta-language
   (`#print axioms` or `TrustedBoundary.lean` `.olean` inspection via
   `Lean.collectAxioms` and `Lean.Kernel.Environment.replay`), forming the
   two-level soundness pair proved in `meta_auditor_two_level_soundness`.
2. **Turing–Rice–Lawvere Undecidability and the Arithmetic Hierarchy
   ($\Delta^0_0, \Sigma^0_1, \Pi^0_1, \Pi^0_2, \Pi^0_3$) of Verification
   Obligations:**
   By Lawvere's Fixed-Point Theorem (Lawvere 1969) and Rice's Theorem (Rice
   1953), no total computable boolean procedure `decideVer : L.Prog → Bool` can
   decide non-trivial semantic correctness `L.Verified pre post p`
   (`rice_verified_undecidable`) or halting/productivity `L.ProductiveOn pre p`
   (`rice_productiveOn_undecidable`) over a universal programming language. In
   the Kleene–Mostowski Arithmetic Hierarchy (Kleene 1943; Mostowski 1947),
   universal safety ($\forall q k,\; \text{pre}(q) \to \text{step}^k(p, q) \neq
   \text{ub}$) is $\Pi^0_1$-complete, universal productivity ($\forall q,\;
   \text{pre}(q) \to \exists k o,\; \text{eval}(p, q, k) = \text{some } o$) is
   $\Pi^0_2$-complete, and unrestricted specification equivalence ($\forall p,\;
   \text{Verified}(S_1, p) \iff \text{Verified}(S_2, p)$) is $\Pi^0_2$/$\Pi^0_3$
   undecidable (`undecidability_of_unrestricted_spec_equivalence`).
3. **Gödel's *Dialectica* Interpretation (1958) & Kreisel's Modified
   Realizability (1959) ($\Sigma^0_1$ Search $\to$ $\Delta^0_0$ Certificate
   Reduction):**
   Whereas universal safety and totality ($\Pi^0_1, \Pi^0_2$) require deductive
   proofs (inductive invariants, ranking functions, or compositional cut
   lemmas), Anneal's anti-vacuity and specification-discrimination obligations
   are **existential ($\Sigma^0_1$)** statements: precondition inhabitation
   ($\exists q,\; \text{pre}(q)$), observable spine non-triviality ($\exists
   o_1 o_2,\; \text{obs}(o_1) \neq \text{obs}(o_2)$), and two-point canary
   separation ($\exists q_0 k_1 k_2 o_1 o_2,\; \text{pre}(q_0) \land
   \text{eval}(p_{\text{good}}, q_0, k_1) = \text{some } o_1 \land
   \text{eval}(p_{\text{bad}}, q_0, k_2) = \text{some } o_2 \land
   \text{obsPost}(q_0, \text{obs}(o_1)) \land \neg \text{obsPost}(q_0,
   \text{obs}(o_2))$). By Skolemizing the existential quantifiers into an
   explicit witness certificate `cert : CanaryCertificate Query` (`(q₀, k_good,
   k_bad)`), verification of the entire anti-vacuity and negative-canary bundle
   collapses from $\Sigma^0_1$ search to a **$\Delta^0_0$ (primitive recursive)
   boolean check** `checkCanaryCertificate ... cert = true` discharged in $O(1)$
   by Lean's kernel via `rfl` (`certificate_discharges_canary_and_nonvacuity`,
   `toy_canary_and_nonvacuity_by_rfl`).
4. **The Formalization / Intent Gap (Naur 1985; Smith 1985; Fetzer 1988; Popper
   1934/1959; Lakatos 1976; Zave & Jackson 1997):**
   Because a human engineer's intended behavior (`HumanIntent : Query → SemObs →
   Prop`) is an unformalized mental theory in the sense of Naur (1985),
   equivalence between `HumanIntent` and a formal specification `(pre, obsPost)`
   is not a formal theorem. Pure $\Pi^0_1$ universal deduction (`L.VerifiedSpine
   pre obsPost p`) is one-sided: it prevents **implementation bugs relative to
   `obsPost`**, but is blind to **under-specification** (`obsPost := True`),
   permitting buggy programs that violate `HumanIntent` to verify cleanly
   (`pure_deduction_blind_to_under_specification`). Pairing $\Pi^0_1$ universal
   deduction on `p_good` with $\Delta^0_0$-checkable **Popperian ground
   falsifiers** (`p_bad` refuted at a concrete ground query `q₀` with distinct
   ground observable `obs o_bad ≠ obs o_good`) and **Lakatosian
   counterexample-driven specification refinement**
   (`lakatos_counterexample_exposes_under_specification_and_refines`) provides
   the strongest mathematically possible guarantee across the formal/informal
   boundary.

## Applicability

The findings and mechanized proofs in this report apply to:

- **Lean 4.34.1 (`leanprover/lean4:v4.34.1`, commit
  `5045d0056413266e57c625dcd7c365b10e377c52`):** specifically kernel
  typechecking, definitional equality (`rfl`), `Lean.collectAxioms`, and
  `Lean.Kernel.Environment.replay` invoked with `-DElab.async=false
  -Ddebug.skipKernelTC=false`.
- **Anneal's Ground-Up Verification Kernel (`Trusted/Refinement.lean` and
  `Trusted/StepResult.lean` in `joshlf/anneal-private#241`) and Boundary Auditor
  (`trusted/audit/TrustedBoundary.lean`):** specifically the division of
  responsibilities between in-kernel `Prop` invariants (`StrictUnitTheorem`,
  `Obligation`, `VerifiedSpineWithCanaries`, `RefutedProductiveOn`) and
  meta-level `.olean` environment inspection.
- **Preserved Mechanization (`support/TractabilityAndIncompleteness.lean`):**
  a standalone 1,095-line, 23-theorem Lean 4.34.1 module (`prelude`,
  `import Init.Core`) whose 23 theorems all verify with **zero axioms** (`[]`:
  zero `sorryAx`, zero `Classical.choice`, zero `Lean.ofReduceBool`, zero
  `propext`, and zero `Quot.sound`).

## Findings

### Finding 1: Gödel's Incompleteness Theorems, Tarski's Undefinability of Truth, and Löb's Theorem — Why the Axiom Boundary Must Live in the Meta-Language

`Basis: normative + source + execution + derived`

#### 1.1 Foundational Literature and Exact Mathematical Theorems

1. **Gödel's First and Second Incompleteness Theorems (Gödel 1931;
   Hilbert & Bernays 1939):**
   - **Citation:** Kurt Gödel, *"Über formal unentscheidbare Sätze der Principia
     Mathematica und verwandter Systeme I"*, *Monatshefte für Mathematik und
     Physik*, Vol. 38, No. 1, pp. 173–198 (1931),
     DOI: `10.1007/BF01700692` (JFM `57.0055.03`). Derivability conditions
     systematized in David Hilbert and Paul Bernays, *Grundlagen der
     Mathematik*, Vol. II, Springer, Berlin (1939), pp. 283–340.
   - **Hilbert–Bernays–Löb Derivability Conditions (`D1`–`D3`):** Let $T$ be a
     recursively axiomatized theory extending Robinson arithmetic $\mathsf{Q}$
     (or primitive recursive arithmetic $\mathsf{PRA}$), and let
     $\text{Prov}_T(\ulcorner \varphi \urcorner)$ (written $\Box \varphi$) be
     the $\Sigma^0_1$ provability predicate asserting that there exists a Gödel
     code $d \in \mathbb{N}$ of a valid $T$-derivation of $\varphi$:
     $$\text{(D1)} \quad T \vdash \varphi \implies T \vdash \Box \varphi$$
     $$\text{(D2)} \quad T \vdash \Box(\varphi \to \psi) \to (\Box \varphi \to \Box \psi)$$
     $$\text{(D3)} \quad T \vdash \Box \varphi \to \Box \Box \varphi$$
   - **Carnap–Gödel Diagonal Lemma (Carnap 1934; Gödel 1931):** For every
     1-place formula $\Psi(x)$ in the language of $T$, there exists a sentence
     $\gamma$ such that $T \vdash \gamma \leftrightarrow \Psi(\ulcorner \gamma
     \urcorner)$.
   - **First Incompleteness Theorem (G1):** If $T$ is consistent, the diagonal
     sentence $G$ satisfying $T \vdash G \leftrightarrow \neg \Box G$ is
     unprovable in $T$ ($T \nvdash G$); if $T$ is $\omega$-consistent (or
     $\Sigma^0_1$-sound, or moved to Rosser's predicate, Rosser 1936), then
     $T \nvdash \neg G$ as well.
   - **Second Incompleteness Theorem (G2):** Define the formal consistency
     statement of $T$ as $\text{Con}(T) :\equiv \neg \Box \bot$ (equivalently,
     $\Box \bot \to \bot$). If $T$ is consistent, then $T$ cannot prove its own
     consistency:
     $$T \text{ is consistent} \implies T \nvdash \text{Con}(T).$$

2. **Tarski's Undefinability of Truth (Tarski 1933/1935):**
   - **Citation:** Alfred Tarski, *"Pojęcie prawdy w językach nauk
     dedukcyjnych"*, Towarzystwo Naukowe Warszawskie, Warsaw (1933); German
     translation *"Der Wahrheitsbegriff in den formalisierten Sprachen"*,
     *Studia Philosophica*, Vol. 1, pp. 261–405 (1935); English translation
     *"The Concept of Truth in Formalized Languages"* in *Logic, Semantics,
     Metamathematics*, Oxford University Press (1956), pp. 152–278.
   - **Theorem (Undefinability of Truth):** Let $\mathcal{L}$ be aninterpreted
     formal language capable of syntax arithmetization (diagonalization) and
     containing classical negation. There exists no formula $\text{True}(x)$ in
     the object language $\mathcal{L}$ satisfying Tarski's Convention T
     ($\text{True}(\ulcorner \varphi \urcorner) \leftrightarrow \varphi$ for all
     sentences $\varphi \in \mathcal{L}$). Any sound truth predicate or
     soundness judgment for the object language $\mathcal{L}$ must be defined in
     a strictly richer **meta-language** $\mathcal{M}$.

3. **Löb's Theorem (Löb 1955):**
   - **Citation:** Martin Hugo Löb, *"Solution of a Problem of Leon Henkin"*,
     *The Journal of Symbolic Logic*, Vol. 20, No. 2, pp. 115–118 (1955),
     DOI: `10.2307/2266895`.
   - **Theorem:** Let $T$ satisfy the Hilbert–Bernays–Löb derivability
     conditions (`D1`–`D3`) and the diagonal lemma. For any sentence $P$, if $T$
     proves that provability of $P$ implies $P$ (the local reflection principle
     for $P$), then $T$ already proves $P$:
     $$T \vdash (\Box \ulcorner P \urcorner \to P) \implies T \vdash P.$$
   - **Immediate Corollary for Self-Certification:** A formal system $T$ can
     prove $\Box \ulcorner P \urcorner \to P$ *only* for sentences $P$ that are
     already unconditionally provable in $T$. In particular, for any unprovable
     sentence (such as $P = \bot$ in a consistent theory), $T \nvdash \Box
     \ulcorner \bot \urcorner \to \bot$.

#### 1.2 Architectural Consequence for Anneal: What Moves Into `Trusted/Refinement.lean` vs. What Must Stay in `TrustedBoundary.lean`

A central engineering question during Pass 2 of `joshlf/anneal-private#241` was:
*How much of `trusted/audit/TrustedBoundary.lean` can be pushed inside Lean's
type theory (`Trusted/Refinement.lean`) so that plain `lake build` enforces it
without an external auditor?*

Tarski's object/meta hierarchy and Gödel–Löb incompleteness provide the exact
mathematical dividing line:

- **Object-Language Properties (Enforceable Inside `Trusted/Refinement.lean`):**
  Every property that is a predicate on **object-level values, types, and
  behaviors** inside a consistent Lean environment can be enforced directly in
  `Trusted/Refinement.lean`:
  1. *Constructor-gated obligations:* Making `Obligation.mk` `private` to
     `Trusted/Refinement.lean` and exposing only the 20 `@[vetted]` smart
     constructors prevents external modules from constructing `{ id := ...,
     prop := True }` at typechecking time (eliminating `trusted/audit` Check 6).
  2. *Zero waivers and non-empty unique obligation inventories:* Defining
     `StrictUnitTheorem u` as `UnitTheorem u ∧ u.waived = [] ∧ NoDupIds
     (u.obligations.map Obligation.id) ∧ AllHold (u.artifacts.map
     EmittedArtifact.holds)` forces `AllHold (u.obligations.map Obligation.prop)`
     inside the Lean kernel regardless of `u.policy` (eliminating Check 5).
  3. *Domain-locked non-vacuity and paired negative canaries:* `Language.dom`
     and `Language.VerifiedSpineWithCanaries` force `∃ q, pre q`, refute
     `obsPost := True`, and refute constant `L.obs` / `SemObs := Unit` inside
     pure `Prop` (`Theory/Challenger4_AuditabilityAndScaling.lean`).

- **Meta-Language Properties (Ineliminable from `#print axioms` /
  `TrustedBoundary.lean`):**
  Conversely, suppose an engineer attempts to eliminate `#print axioms` or
  `TrustedBoundary.lean` by adding an internal proposition `InternalNoSorryProp :
  Prop` to `StrictUnitTheorem`:
  ```lean
  def SelfCertifiedUnitTheorem (u : VerificationUnit Id)
      (InternalNoSorryProp : Prop) : Prop :=
    StrictUnitTheorem u ∧ InternalNoSorryProp
  ```
  As mechanized in **Theorem 2.1 (`internal_self_certification_explodes`)** and
  **Theorem 2.2 (`internal_conjunct_cannot_detect_sorryAx`)** of
  `support/TractabilityAndIncompleteness.lean`:
  - In Lean 4, `sorry` elaborates to an application of the polymorphic axiom
    `sorryAx : ∀ {α : Sort u} (synthetic : Bool), α`.
  - When a proof script invokes `sorry` (or declares `axiom bad : False`, or
    uses `Lean.ofReduceBool` with a spoofed `@[implemented_by]` function), the
    local deduction context contains `h_sorryAx : ∀ (P : Prop), P`.
  - Applying `h_sorryAx` proves `StrictUnitTheorem u` and `InternalNoSorryProp`
    with identical ease: `⟨h_sorryAx (StrictUnitTheorem u), h_sorryAx
    InternalNoSorryProp⟩`.
  - By **Theorem 2.3 (`abstract_lob_theorem`)** and **Theorem 2.4
    (`godel_second_incompleteness_from_lob`)**, even if `InternalNoSorryProp` is
    defined via Gödel numbering of Lean expressions, no consistent formal system
    can internally certify its own non-contradiction ($\neg \Box \bot$).
  - Therefore, verifying that the `.olean` environment replayed by the kernel is
    free of `sorryAx`, `Classical.choice`, `Lean.ofReduceBool`, `unsafe`,
    `partial`, and `@[implemented_by]` **must** occur in the Tarskian
    meta-language (`checkAxiomFootprint cert = true` over `ConstantInfo` /
    `Lean.collectAxioms`), as proved in **Theorem 2.5
    (`meta_auditor_two_level_soundness`)**.

---

### Finding 2: Turing's Halting Problem, Lawvere's Diagonal Theorem, Rice's Theorem, and the Arithmetic Hierarchy of Verification Obligations

`Basis: normative + source + execution + derived`

#### 2.1 Foundational Literature and Exact Mathematical Theorems

1. **Turing's Halting Problem (Turing 1936/1937):**
   - **Citation:** Alan M. Turing, *"On Computable Numbers, with an Application
     to the Entscheidungsproblem"*, *Proceedings of the London Mathematical
     Society*, Series 2, Vol. 42, No. 1, pp. 230–265 (received May 1936,
     published 1937), DOI: `10.1112/plms/s2-42.1.230`.
   - **Theorem:** There is no Turing machine (total computable function) that
     decides, given the description $\ulcorner M \urcorner$ of an arbitrary
     machine and input $q$, whether $M(q)$ halts ($\exists k,\; \text{step}^k(M,
     q) = \text{halted}$). The halting set $K = \{\langle e, q \rangle \mid
     \varphi_e(q)\downarrow\}$ is $\Sigma^0_1$-complete (recursively enumerable
     but not recursive).

2. **Rice's Theorem (Rice 1953):**
   - **Citation:** Henry Gordon Rice, *"Classes of Recursively Enumerable Sets
     and Their Decision Problems"*, *Transactions of the American Mathematical
     Society*, Vol. 74, No. 2, pp. 358–366 (1953),
     DOI: `10.1090/S0002-9947-1953-0053041-6`.
   - **Theorem:** Let $\mathcal{F}$ be any class of partial recursive functions,
     and let $I_{\mathcal{F}} = \{e \in \mathbb{N} \mid \varphi_e \in
     \mathcal{F}\}$ be its index set. The set $I_{\mathcal{F}}$ is recursive
     (decidable) if and only if $\mathcal{F} = \emptyset$ or $\mathcal{F}$ is the
     class of all partial recursive functions. Every non-trivial extensional
     (semantic) property of programs is undecidable.

3. **Lawvere's Fixed-Point Theorem (Lawvere 1969; Yanofsky 2003):**
   - **Citation:** F. William Lawvere, *"Diagonal Arguments and Cartesian Closed
     Categories"*, in *Category Theory, Homology Theory and their Applications
     II*, Lecture Notes in Mathematics, Vol. 92, Springer, Berlin, pp. 134–145
     (1969), DOI: `10.1007/BFb0080769`. Unified survey in Noson S. Yanofsky,
     *"A Universal Approach to Self-Referential Paradoxes, Incompleteness and
     Fixed Points"*, *The Bulletin of Symbolic Logic*, Vol. 9, No. 3,
     pp. 362–386 (2003), DOI: `10.2178/bsl/1058448677`.
   - **Theorem:** In any cartesian closed category (or type theory), if
     $e : A \times A \to B$ is weakly point-surjective onto $A \to B$, then
     every endomorphism $f : B \to B$ has a fixed point $b \in B$ with
     $f(b) = b$. Contrapositively (`lawvere_diagonal_no_surjection`), if
     $\text{neg} : \text{Val} \to \text{Val}$ has no fixed point ($\forall v,\;
     \text{neg}(v) \neq v$, such as boolean negation `!` on `Bool`), no program
     $p_0 \in \text{Prog}$ can compute the diagonal negation $\lambda p.\;
     \text{neg}(\text{eval}(p, p))$.
   - **Constructive Instantiation to `Language SemObs` (`Theorem 3.2`,
     `rice_semantic_undecidability`, and `Theorem 3.3`,
     `rice_verified_undecidable`):** For any language `L : Language SemObs`
     closed under diagonal branching (`HasDiagonalBranching L`) and any
     specification `(pre, post)` that admits at least one valid program
     `goodProg` (`L.Verified pre post goodProg`) and refutes at least one buggy
     program `badProg` (`L.Refuted pre post badProg`), no total boolean function
     `decideVer : L.Prog → Bool` can decide `L.Verified pre post p` for all
     `p : L.Prog`. Similarly, **Theorem 3.4 (`rice_productiveOn_undecidable`)**
     proves that no total boolean function can decide `L.ProductiveOn pre p`.

4. **The Kleene–Mostowski Arithmetic Hierarchy (Kleene 1943; Mostowski 1947;
   Rogers 1967):**
   - **Citations:**
     - Stephen Cole Kleene, *"Recursive Predicates and Quantifiers"*,
       *Transactions of the American Mathematical Society*, Vol. 53, No. 1,
       pp. 41–73 (1943), DOI: `10.1090/S0002-9947-1943-0007371-8`.
     - Andrzej Mostowski, *"On Definable Sets of Positive Integers"*,
       *Fundamenta Mathematicae*, Vol. 34, No. 1, pp. 81–112 (1947),
       DOI: `10.4064/fm-34-1-81-112`.
     - Hartley Rogers Jr., *Theory of Recursive Functions and Effective
       Computability*, McGraw-Hill, New York (1967; MIT Press edition 1987).
   - **Hierarchy Definition:**
     - $\Delta^0_0 = \Sigma^0_0 = \Pi^0_0$: formulas with only bounded
       quantifiers over computable predicates (decidable in finite time by
       primitive recursive evaluation / Lean kernel WHNF reduction `rfl` or
       `decide`).
     - $\Sigma^0_{n+1}$: formulas of the form $\exists x_1 \cdots \exists x_k\,
       \psi$ where $\psi \in \Pi^0_n$. ($\Sigma^0_1$ = recursively enumerable /
       semi-decidable).
     - $\Pi^0_{n+1}$: formulas of the form $\forall x_1 \cdots \forall x_k\,
       \psi$ where $\psi \in \Sigma^0_n$. ($\Pi^0_1$ = co-r.e.; $\Pi^0_2$ =
       $\forall \exists$, the class of total recursive functions `Tot`).
     - $\Delta^0_n = \Sigma^0_n \cap \Pi^0_n$; by Post's Theorem (Post 1944),
       $\Delta^0_1$ is the class of recursive (decidable) sets.

#### 2.2 Complete Arithmetic Hierarchy Classification Table of Anneal's Obligations

Assuming a computable single-step relation / fuel evaluator
`eval : Prog → Query → Nat → Option Out`, computable observable projection
`obs : Out → SemObs`, and decidable ground predicates `preB : Query → Bool` and
`obsPostB : Query → SemObs → Bool`, every obligation in Anneal's verification
and anti-pathology architecture occupies a precise level of the Arithmetic
Hierarchy:

| Obligation / Property | Logical Quantifier Prefix | Unassisted Complexity Class | Complexity Class with Explicit Witness Certificate | Anneal Mechanism & Discharge Method |
| :--- | :--- | :--- | :--- | :--- |
| **1. Bounded $k$-step execution & ground postcondition** | Quantifier-free: $\text{eval}(p, q_0, k_0) = \text{some } o \land \text{obsPostB}(q_0, \text{obs}(o)) = \text{true}$ | **$\Delta^0_0$ (Decidable)** | **$\Delta^0_0$ (Decidable)** | Kernel WHNF reduction (`by rfl` or `by decide`) |
| **2. Precondition non-vacuity (`InhabitedPre`)** | $\exists q,\; \text{pre}(q)$ | **$\Sigma^0_1$-complete** (semi-decidable search over infinite `Query`) | **$\Delta^0_0$ (Decidable)** given concrete witness $q_0$ (`preB q₀ = true`) | `Or.inl ⟨q₀, rfl⟩` in `NonVacuousOn` (or derived automatically from `CanaryCertificate`) |
| **3. Pointwise productivity at query $q_0$** | $\exists k\, o,\; \text{eval}(p, q_0, k) = \text{some } o$ | **$\Sigma^0_1$-complete** (Halting problem at $q_0$, Turing 1936) | **$\Delta^0_0$ (Decidable)** given concrete step fuel $k_0$ (`eval p q₀ k₀ = some o`) | Fuel evaluation `BB5.DetMachine.runSteps` / `CanaryCertificate` (`rfl`) |
| **4. Non-constant observable projection (`obs`) & non-subsingleton `SemObs`** | $\exists o_1\, o_2,\; \text{obs}(o_1) \neq \text{obs}(o_2)$ | **$\Sigma^0_1$** (search for two distinct outcomes) | **$\Delta^0_0$ (Decidable)** given $o_{\text{good}}, o_{\text{bad}}$ from `eval` at $q_0$ | Derived automatically by `verifiedSpineWithCanaries_refutes_constant_obs` and `certificate_discharges_canary_and_nonvacuity` |
| **5. Two-point productive negative-canary separation (`CanaryCertificate`)** | $\exists q_0\, k_1\, k_2\, o_1\, o_2,\; \text{pre}(q_0) \land \text{eval}(p_{\text{good}}, q_0, k_1) = \text{some } o_1 \land \text{eval}(p_{\text{bad}}, q_0, k_2) = \text{some } o_2 \land \text{obsPost}(q_0, \text{obs}(o_1)) \land \neg \text{obsPost}(q_0, \text{obs}(o_2))$ | **$\Sigma^0_1$-complete** to discover $(q_0, k_1, k_2)$ | **$\Delta^0_0$ (Decidable)** given `cert := ⟨q₀, k_good, k_bad⟩`! | `checkCanaryCertificate ... cert = true` (`rfl`) + `certificate_discharges_canary_and_nonvacuity` |
| **6. Universal safety / partial correctness (`L.sem p ≤ L.SpecOn pre post`)** | $\forall q\, k,\; \text{pre}(q) \to \text{step}^k(p, q) \neq \text{failed} \land (\text{step}^k(p, q) = \text{term}(o) \to \text{post}(q, o))$ | **$\Pi^0_1$-complete** (co-r.e.; undecidable by Rice 1953) | **$\Delta^0_0$** on finite `Query` $\times$ bounded loops; otherwise requires deductive invariant | Deductive proof in `Proof.lean` (Hoare/WP, abstract interpretation `Abstracts`, or bounded `runSteps`) |
| **7. Universal productivity / total correctness (`L.ProductiveOn pre p`)** | $\forall q,\; \text{pre}(q) \to \exists k\, o,\; \text{eval}(p, q, k) = \text{some } o$ | **$\Pi^0_2$-complete** (`Tot`-complete; strictly harder than Halting) | **$\Pi^0_1 \to \Delta^0_0$** when Skolemized by a computable fuel bound $K(q)$ (`eval p q (K q)`) | `BB5.DetMachine.verifiedOn_of_runSteps` or ranking function `loopCut_ranking_runSteps` |
| **8. Infinite reactive liveness (`.reacts tr` in `EventualBehaviorOf`)** | $\forall q,\; \text{pre}(q) \to \exists n\, s,\; \text{ReachesPrefix}(n, \text{tr}, s) \land \forall k,\; \exists s'\, \text{tr}',\; \text{ReachesPrefix}(k, \text{tr}', s')$ | **$\Pi^0_2$ / $\Sigma^0_2$** (unbounded ongoing continuation) | Deductive loop-invariant cut over one reactive cycle | `BB4` / `Stitcher5c` periodic reactive loop cut |
| **9. Unrestricted specification equivalence** | $\forall p,\; \text{Verified}(S_1, p) \leftrightarrow \text{Verified}(S_2, p)$ | **$\Pi^0_2$ / $\Pi^0_3$ (Undecidable)** | Replaced by **witnessed 2-point separation** ($\Delta^0_0$) on concrete mutants `badProgs` | `VerifiedSpineWithCanaries` + `CanaryCertificate` (`rfl`) |

---

### Finding 3: Gödel's *Dialectica* Interpretation (1958) & Kreisel's Modified Realizability (1959) — Collapsing $\Sigma^0_1$ Anti-Vacuity Obligations to $\Delta^0_0$ Kernel `rfl` Checks

`Basis: normative + source + execution + derived`

#### 3.1 Foundational Literature

1. **Gödel's *Dialectica* Interpretation (Gödel 1958):**
   - **Citation:** Kurt Gödel, *"Über eine bisher noch nicht benützte
     Erweiterung des finiten Standpunktes"*, *Dialectica*, Vol. 12, No. 3–4,
     pp. 280–287 (1958), DOI: `10.1111/j.1746-8361.1958.tb01464.x`.
   - **Core Translation:** Every arithmetic formula $\varphi$ is translated into
     a functional form $\varphi^D :\equiv \exists x \forall y\, A_0(x, y)$ where
     $x, y$ are functionals of finite type over system $\mathsf{T}$ and $A_0$ is
     **quantifier-free ($\Delta^0_0$, decidable)**. For a purely existential
     ($\Sigma^0_1$) formula $\exists x\, A_0(x)$, the universal quantifier is
     vacuous, so supplying the concrete witness term $x_0$ reduces verification
     of $\varphi$ to the decidable $\Delta^0_0$ matrix $A_0(x_0)$.

2. **Kreisel's Modified Realizability (Kreisel 1959):**
   - **Citation:** Georg Kreisel, *"Interpretation of Analysis by Means of
     Constructive Functionals of Finite Types"*, in *Constructivity in
     Mathematics: Proceedings of the Colloquium Held at Amsterdam, 1957* (ed.
     Arend Heyting), North-Holland, Amsterdam, pp. 101–128 (1959).
   - **Core Principle:** In constructive type theory (and Lean 4's Calculus of
     Inductive Constructions), a proof of an existential or negative-refutation
     statement over a step-indexed operational semantics is realized by a finite
     tuple of witness terms (query $q_0$ and step budgets $k_{\text{good}},
     k_{\text{bad}}$) paired with a decidable computation check.

#### 3.2 Asymmetric Tractability of Verification vs. Anti-Vacuity (`Section 4` of `support/TractabilityAndIncompleteness.lean`)

The Arithmetic Hierarchy table in Section 2.2 reveals a profound **tractability
asymmetry** between proving a program correct and proving that a specification
is non-vacuous and refutes a mutant:

- **Proving `goodProg` correct (`L.VerifiedSpine pre obsPost goodProg`) is
  $\Pi^0_1 / \Pi^0_2$ ($\forall q \in \text{Query}$):** It quantifies
  universally over all valid queries and all execution paths, so it cannot be
  discharged by testing a single input; it requires a deductive proof.
- **Refuting a mutant `badProg` (`L.RefutedOn ... badProg`) and proving
  specification non-vacuity (`InhabitedPre`, non-trivial `obsPost`, non-constant
  `L.obs`, non-subsingleton `SemObs`, and `L.sem goodProg ≠ L.sem badProg`) are
  $\Sigma^0_1$ ($\exists q_0, k_{\text{good}}, k_{\text{bad}}$)!**
  Why? Because refuting a universal claim $\neg (\forall q,\; P(q))$ requires
  exhibiting **only one counterexample query $q_0$** and running the operational
  evaluator for a finite number of steps $k_{\text{bad}}$!

In **Section 4 of `support/TractabilityAndIncompleteness.lean`**, we formalize
this reduction via `ComputableLang`, `CanaryCertificate`, and
`checkCanaryCertificate`:

```lean
structure CanaryCertificate (Query : Type) where
  q₀     : Query
  k_good : Nat
  k_bad  : Nat

def checkCanaryCertificate {Prog Query Out SemObs : Type}
    (eval : Prog → Query → Nat → Option Out)
    (obs : Out → SemObs)
    (preB : Query → Bool)
    (obsPostB : Query → SemObs → Bool)
    (p_good p_bad : Prog)
    (cert : CanaryCertificate Query) : Bool :=
  preB cert.q₀ &&
  match eval p_good cert.q₀ cert.k_good with
  | none => false
  | some o_good =>
    match eval p_bad cert.q₀ cert.k_bad with
    | none => false
    | some o_bad =>
        obsPostB cert.q₀ (obs o_good) && !(obsPostB cert.q₀ (obs o_bad))
```

**Theorem 4.1 (`certificate_discharges_canary_and_nonvacuity`, zero axioms)**
proves that whenever `checkCanaryCertificate eval obs preB obsPostB p_good p_bad
cert = true` holds (which is a $\Delta^0_0$ boolean equality checkable by
literal `rfl`!), the Lean kernel automatically derives **all eight**
anti-Goodhart and negative-canary properties with zero manual proof steps:

1. `∃ q, preB q = true` (strictly inhabited precondition),
2. `∃ o_good o_bad : Out, obs o_good ≠ obs o_bad` (distinct observable spine
   values),
3. `¬ (∀ o₁ o₂ : Out, obs o₁ = obs o₂)` (non-constant observable projection
   `L.obs`),
4. `¬ (∀ s₁ s₂ : SemObs, s₁ = s₂)` (non-subsingleton `SemObs`, refuting
   `SemObs = Unit`),
5. `¬ (∀ q o, preB q = true → obsPostB q (obs o) = true)` (non-trivial
   postcondition),
6. `L.sem p_good ≠ L.sem p_bad` (program-discriminating semantics, given
   step-determinism of `p_good` at `cert.q₀`),
7. `L.RefutedOn dom (fun q => preB q = true) (fun q o => obsPostB q (obs o) = true) p_bad`
   (in-kernel negative canary refutation of `p_bad`), and
8. `L.RefutedProductiveOn dom (fun q => q = cert.q₀ ∧ preB q = true) (fun q o => obsPostB q (obs o) = true) p_bad`
   (pointwise productive negative-canary refutation at `cert.q₀`).

As demonstrated in **Theorem 4.2 (`toy_canary_and_nonvacuity_by_rfl`)**,
supplying `toyCert := ⟨7, 1, 1⟩` discharges `toyCert_valid_by_rfl` by literal
`rfl`, proving all eight properties in $O(1)$ kernel reduction!

---

### Finding 4: The Formalization / Intent Gap — Why Pairing $\Pi^0_1$ Universal Deduction with $\Delta^0_0$ Popperian Ground Falsifiers Is Mathematically Optimal

`Basis: documentation + source + execution + derived`

#### 4.1 Foundational Literature on the Formal/Informal Boundary

1. **DeMillo, Lipton & Perlis (1979):**
   - **Citation:** Richard A. DeMillo, Richard J. Lipton, and Alan J. Perlis,
     *"Social Processes and Proofs of Theorems and Programs"*, *Communications
     of the ACM*, Vol. 22, No. 5, pp. 271–280 (May 1979),
     DOI: `10.1145/359104.359106`.
   - **Thesis:** Contrasts mathematical proofs (checked through social scrutiny
     of high-level ideas) with program verification obligations, warning that
     isolated formal derivations without independent falsification channels risk
     validating artifacts whose specifications silently diverge from reality.

2. **Peter Naur (1985):**
   - **Citation:** Peter Naur, *"Programming as Theory Building"*,
     *Microprocessing and Microprogramming*, Vol. 15, No. 5, pp. 253–264 (May
     1985), DOI: `10.1016/0165-6074(85)90032-8`.
   - **Thesis:** A programmer's knowledge of how a problem maps onto program
     execution constitutes an unformalized mental *Theory* (`HumanIntent`) that
     cannot be exhaustively reduced to any finite set of written rules or formal
     specifications. Any formal specification $S$ is an incomplete projection of
     that mental theory.

3. **Brian Cantwell Smith (1985):**
   - **Citation:** Brian Cantwell Smith, *"The Limits of Correctness"*, *ACM
     SIGCAS Computers and Society*, Vol. 14–15, No. 1–4, pp. 18–26 (1985),
     DOI: `10.1145/379486.379512` (also presented at the *Symposium on
     Unintended Nuclear War*, 1985).
   - **Thesis:** "Correctness" in formal verification is a **relational**
     property between two formal models (a program model and a specification
     model), separated from the real world (and from human intent) by the gap of
     *registration* (modeling). A proof of `L.sem p ≤ Spec` proves relative
     consistency between two formal objects; it does not by itself prove that
     either formal object faithfully models the intended domain.

4. **James H. Fetzer (1988):**
   - **Citation:** James H. Fetzer, *"Program Verification: The Very Idea"*,
     *Communications of the ACM*, Vol. 31, No. 9, pp. 1048–1063 (September
     1988), DOI: `10.1145/48529.48530` (and ACM Technical Correspondence
     responses in *CACM* 32(3):287–290 and 32(4):506–512, 1989).
   - **Thesis:** Distinguishes pure deductive validity within an abstract formal
     calculus from empirical/causal adequacy of the operational model `L.sem`
     and specification `Spec`.

5. **Jeannette M. Wing (1990), Pamela Zave & Michael Jackson (1997), and Leslie
   Lamport (2002):**
   - **Citations:**
     - Jeannette M. Wing, *"A Specifier's Introduction to Formal Methods"*,
       *IEEE Computer*, Vol. 23, No. 9, pp. 8–24 (September 1990),
       DOI: `10.1109/2.58215`.
     - Pamela Zave and Michael Jackson, *"Four Dark Corners of Requirements
       Engineering"*, *ACM Transactions on Software Engineering and Methodology
       (TOSEM)*, Vol. 6, No. 1, pp. 1–30 (January 1997),
       DOI: `10.1145/237432.237434`.
     - Leslie Lamport, *Specifying Systems: The TLA+ Language and Tools for
       Hardware and Software Engineers*, Addison-Wesley, Boston (2002).
   - **Thesis (Zave & Jackson's $K, S \vdash R$ Law):** Domain knowledge $K$
     (semantics `L.sem`, target ISA `X86Lang`, and codec `BehaviorCodec`) and
     machine specification $S$ (`pre`, `obsPost`) must entail user requirements
     $R$ (`HumanIntent`) expressed over **shared ground phenomena** at the
     environment boundary (`SemObs`), never over internal machine-private
     abstractions (`Out`).

6. **Karl Popper (1934/1959) and Imre Lakatos (1976):**
   - **Citations:**
     - Karl R. Popper, *Logik der Forschung*, Julius Springer, Vienna (1934);
       English translation *The Logic of Scientific Discovery*, Hutchinson,
       London (1959).
     - Imre Lakatos, *Proofs and Refutations: The Logic of Mathematical
       Discovery* (eds. John Worrall and Elie Zahar), Cambridge University
       Press, Cambridge (1976), DOI: `10.1017/CBO9781139171472`.
   - **Thesis:** Universal theories ($\forall q,\; P(q)$) cannot be inductively
     verified by finite positive instances, because a tautological theory
     ($P(q) :\equiv \text{True}$) is consistent with every positive instance. A
     theory has empirical/semantic content *if and only if* it forbids specific
     observable states (**Popperian falsifiability**). When a false positive
     counterexample (`p_bad`) slips through a candidate definition or theorem,
     the specification is strengthened via **Lakatosian lemma-incorporation /
     monster-barring** until the counterexample is refuted.

#### 4.2 Synthesis: The Exact Boundary of Formalizability in Anneal (`Section 5` of `support/TractabilityAndIncompleteness.lean`)

Why can't any formal framework prove inside Lean that `obsPost` equals the
engineer's unformalized mental concept `HumanIntent`?

1. **By Naur (1985) and Smith (1985):** `HumanIntent` is not a formal object
   until someone writes a formal definition for it; writing a second formal
   specification `Spec₂` and proving `Spec₁ ↔ Spec₂` merely shifts the intent
   gap from `Spec₁` to `Spec₂` (and by **Theorem 3.5**, checking unrestricted
   specification equivalence across programs is $\Pi^0_2/\Pi^0_3$ undecidable).
2. **By Theorem 5.1 (`pure_deduction_blind_to_under_specification`):** Pure
   $\Pi^0_1$ universal verification (`L.VerifiedSpine pre obsPost p`) checks
   only the **upper bound** `L.sem p ≤ L.SpineSpecOn pre obsPost`. If `obsPost`
   is under-specified (`obsPost := fun _ _ => True`), a buggy program `p_bad`
   that violates `HumanIntent` at `(q₀, o_bad)` still satisfies
   `L.VerifiedSpine` unconditionally.
3. **Why Ground-Observable Popperian Falsifiers Close the Gap (`Theorem 5.2`,
   `lakatos_counterexample_exposes_under_specification_and_refines`):**
   While humans cannot reliably eyeball a 500-line quantifier-heavy formal
   specification `obsPost` or operational semantics `L.sem` for subtle polarity
   inversions, humans *can* immediately recognize concrete ground-type values
   (e.g., at input `q₀ = 7`, `p_good` must return `8` and `p_bad` returning `7`
   is wrong).
   By anchoring `obsPost` to the boundary observable spine `SemObs` (Zave &
   Jackson's shared ground phenomena) and pairing universal deduction on
   `p_good` ($\Pi^0_1$) with a $\Delta^0_0$-checkable negative canary `p_bad`
   (`VerifiedSpineWithCanaries` + `CanaryCertificate`), Anneal pins the formal
   specification from **both sides**:
   - **From below ($\Pi^0_1$ universal deduction + `ProductiveOn`):** `p_good`
     is defined, productive, and satisfies `obsPost` on *every* query $q \in
     \text{pre}$ (blocking over-specification and implementation bugs).
   - **From above ($\Delta^0_0$ Popperian falsifier `p_bad` at `q₀`):** `p_bad`
     is productive yet refuted by `obsPost` at `q₀` (blocking
     under-specification `obsPost := True`, blocking `SemObs := Unit` / constant
     `L.obs`, blocking `pre := False` / `dom := False`, and forcing
     `L.sem p_good ≠ L.sem p_bad`).

Under Gödel, Tarski, Rice, and Naur, this **two-sided sandwich** ($\Pi^0_1$
universal deduction below + $\Delta^0_0$ witnessed ground falsifiers above +
Tarskian meta-language `.olean` axiom audit outside) is the strongest
mathematically possible guarantee for a formal verification framework.

## Boundaries

- **Known not to apply (In-Kernel Detection of `sorryAx` or Unsound Axioms):**
  By Theorems 2.1–2.4, no object-language `Prop` modification to
  `StrictUnitTheorem` can replace the meta-language check (`#print axioms` or
  `TrustedBoundary.lean`) that the proof environment is free of `sorryAx`,
  `Classical.choice`, `Lean.ofReduceBool`, `@[implemented_by]`, and `unsafe`.
- **Known not to apply (Unassisted Decidability of `L.Verified` or
  `L.ProductiveOn`):**
  By Theorems 3.2–3.5, no total computable decision procedure can decide
  `L.Verified pre post p` or `L.ProductiveOn pre p` for arbitrary programs in a
  Turing-complete language without deductive invariants or fuel bounds.
- **Known not to apply (Pointwise Canary Sufficiency for Universal Alignment):**
  A finite set of negative canaries `badProgs` refutes under-specification along
  every tested mutation axis (and unconditionally refutes `pre := False`,
  `obsPost := True`, and constant `L.obs`), but because `Query` is in general
  infinite, a finite canary list cannot by itself prove that `obsPost` matches
  an unformalized `HumanIntent` on untested mutation axes outside `badProgs`.

## Evidence

- **Mechanized Lean 4.34.1 Artifact:**
  `support/TractabilityAndIncompleteness.lean` (1,095 lines, 23 theorems,
  compiled with `lean -DElab.async=false -Ddebug.skipKernelTC=false`,
  exit code `0`, 0 warnings, and `#print axioms` confirming `does not depend on
  any axioms` for all 23 theorems):
  - *Section 2 (Tarski / Gödel / Löb Meta-Boundary):*
    `internal_self_certification_explodes` (lines 345–350),
    `internal_conjunct_cannot_detect_sorryAx` (lines 359–364),
    `HBLSystem.d2_box` / `d3_box` / `lift2` (lines 384–401),
    `abstract_lob_theorem` (lines 422–443),
    `godel_second_incompleteness_from_lob` (lines 451–456),
    `meta_auditor_two_level_soundness` (lines 515–555).
  - *Section 3 (Lawvere & Constructive Rice Undecidability):*
    `lawvere_diagonal_no_surjection` (lines 573–580),
    `rice_semantic_undecidability` (lines 598–626),
    `rice_verified_undecidable` (lines 634–647),
    `rice_productiveOn_undecidable` (lines 656–668),
    `undecidability_of_unrestricted_spec_equivalence` (lines 674–685).
  - *Section 4 (Dialectica / Realizability $\Sigma^0_1 \to \Delta^0_0$
    Certificate Reduction):*
    `ComputableLang` (lines 705–718),
    `CanaryCertificate` & `checkCanaryCertificate` (lines 738–757),
    `certificate_discharges_canary_and_nonvacuity` (lines 793–889),
    `toyCert_valid_by_rfl` (lines 932–935),
    `toy_canary_and_nonvacuity_by_rfl` (lines 955–978).
  - *Section 5 (Formalization / Intent Gap, Popperian Falsifiers & Lakatosian
    Refinement):*
    `pure_deduction_blind_to_under_specification` (lines 1020–1039),
    `lakatos_counterexample_exposes_under_specification_and_refines` (lines
    1056–1091).
- **Cross-Referenced Corpus Reports & Ground-Up Framework Artifacts:**
  - `trusted/lean/Trusted/Refinement.lean` and `trusted/audit/TrustedBoundary.lean`.
  - `reports/anneal-tcb-realizability-proof-gated-compilation-and-audit-probes-2026/REPORT.md`
    (Findings 1, 4, 5, and 6 on `hTcb` vacuity, `ScopedVerificationResult`,
    `BoundaryCanarySuite`, and `TrustedBoundary.lean` elaboration probes).
  - `reports/anneal-two-stage-preaudit-olean-axiom-stubbing-and-conservativity-2026/REPORT.md`
    (Findings 1–5 on `Lean.Kernel.Environment.replay`, C++ kernel reducibility,
    and `ConservativityModel.lean`).

## Revalidation

Run the standalone Lean 4.34.1 kernel check and zero-axiom verification script:

```bash
lean \
  -DElab.async=false -Ddebug.skipKernelTC=false \
  support/TractabilityAndIncompleteness.lean
```

A passing run exits with code `0` and zero warnings, confirming that all 23
theorems in Sections 2–5 elaborate and typecheck in the Lean 4.34.1 kernel
under `prelude` and `import Init.Core` with zero axioms.
