# Relational Logics, Simulation Techniques, and Completeness Theorems for Compiler Derivations

## Summary

A verified compiler derivation format must reconcile two distinct requirements:
an **expressive relational judgment** capable of justifying multi-step CFG
optimizations, memory layout transformations, and loop restructuring, and a
**decidable certificate-checking discipline** with a clear completeness
contract. This report synthesizes the logical machinery across relational
program logics, simulation diagrams, cross-shape loop alignment, and
derivation-format completeness, backed by a standalone, zero-`sorry` Lean
`v4.34.1` mechanization (`support/RelationalLogicsAndCompleteness.lean`):

1. **Relational Judgments and $2$-Product Reduction (`rhl_iff_product_hoare`):**
   Benton's Relational Hoare Logic (RHL, POPL 2004), Barthe-Crespo-Kunz
   $2$-product programs (FM 2011), and Sousa-Dillig Cartesian Hoare Logic (PLDI
   2016) reduce relational equivalence $\langle P \rangle\, c_1 \sim c_2 \,\langle Q \rangle$
   to a unary Hoare triple over a synchronized product transition system
   `ProductCmd c1 c2`. While Kleene Algebra with Tests (KAT, Kozen & Patron
   2000) is PSPACE-complete and complete over uninterpreted regular control
   schemata, first-order product programs achieve **Cook-style relative
   completeness** whenever the product schedule aligns loop cut-points.
2. **Simulation Diagrams, Stuttering Measures, and Forward-to-Backward Flip
   (`forward_to_backward_lockstep`):** CompCert-style variable-step forward
   simulations (`ForwardMeasureSim`) relate each source step to $0, 1, \text{or } n$
   target steps via a well-founded stuttering measure $\mu : S_1 \to \mathbb{N}$
   (`s2 = s2' -> mu s1' < mu s1`). Because safe compilation requires preserving
   behavior against target nondeterminism (backward simulation), the compiler
   proves **forward simulations per pass** and flips their composition into a
   **backward simulation** at the top level using **target determinism**
   (`TargetDeterministic`) and **source progress/receptiveness**
   (`forward_to_backward_lockstep`).
3. **Memory Injections (`translatePtr_compose`), Open/Parametric Simulations,
   and Step-Indexed Logical Relations (`Simuliris`, `ReLoC`):** CompCert memory
   injections `MemInj := BlockId -> Option (BlockId * Int)` compose
   associatively (`MemInj.compose`) and translate pointer offsets functorially
   (`translatePtr_compose`), enabling stack-slot coalescing, dead-allocation
   dropping (`f b = none`), and inlining. For open modules and higher-order or
   concurrent code, Hur-Dreyer-Neis-Vafeiadis parametric bisimulations (POPL
   2012), CompCertM's mixed simulations (POPL 2020), ReLoC (LICS 2018), and
   Simuliris (`gitlab.mpi-sws.org/iris/simuliris` @ `e3abfcdc301f`) replace
   global block-ID identity with local frame-preserving bijection/injection
   invariants. Crucially, as established in the corpus's Iris adequacy package,
   **step-indexed $\triangleright$ (later) modalities without transfinite or
   stuttering-measure bounds prove only safety/termination-insensitive
   refinement**, whereas CompCert-style well-founded $\mathbb{N}$ measures (or
   Transfinite Iris $\omega_1$ ordinals) preserve divergence and liveness.
4. **Equivalence of Loops Whose Shapes Differ (`unroll2_loop_alignment` and
   `vectorize4_loop_alignment`):** Structural RHL fails when loop trip counts
   change under unrolling, peeling, or SIMD vectorization. Equivalence is
   restored by **$(k, 1)$-lockstep product alignment with an explicit remainder
   epilogue** (`runUnrolled2WithEpilogue`, proved equivalent to `runScalarLoop`
   for all $n \in \mathbb{N}$ in `unroll2_loop_alignment`) and **homomorphic
   lane packing** (`simdMap4`, proved in `vectorize4_loop_alignment`).
5. **Three Distinct Notions of Completeness (`checkRelDeriv_iff_valid`):**
   By Rice's and Gödel's theorems, no recursive validator is *semantically
   complete* for all equivalent Turing-complete programs. A compiler derivation
   format instead targets three attainable theorems:
   - **Check-Completeness (Decidable Proof Checking):** Given a candidate
     derivation certificate $d$, the boolean checker `checkRelDeriv d c1 c2 delta`
     terminates in linear time and is **both sound and complete with respect to
     the inductive derivation judgment** (`checkRelDeriv d c1 c2 delta = true <->
     ValidRelDeriv d c1 c2 delta`, mechanized in `checkRelDeriv_iff_valid`).
   - **Relative Deductive Completeness (Cook / Product-Program Completeness):**
     Every semantically valid pair in a target alignment class has a valid
     derivation relative to an oracle for the assertion logic (`rhl_iff_product_hoare`).
   - **Pass-Emit Completeness (Translation-Relation Totality):** For a specific
     verified or certifying compiler pass $T$, whenever $T(c_1) = \text{some}(c_2, d)$,
     `checkRelDeriv d c1 c2 = true`.

## Applicability

This report extends `iris-adequacy-transfinite-liveness-simuliris-and-lean-separation-logic`,
`anneal-behavior-codec-and-partial-compile-refinement-algebra`, and
`anneal-mir-to-x86-compiler-vcgen-and-variable-step-refinement`. Its judgment
forms and completeness theorems apply directly to the design of a Lean `v4.34.1`
(`5045d0056413266e57c625dcd7c365b10e377c52`) derivation checker and IR refinement
tower for Rust `1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`). All
mechanized theorems in `support/RelationalLogicsAndCompleteness.lean` depend
only on standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`), with
`rhl_iff_product_hoare` and `forward_to_backward_lockstep` requiring **zero
axioms**.

## Findings

### 1. Relational Program Logics, Product Programs, and KAT

Basis: documentation + source + execution (`support/RelationalLogicsAndCompleteness.lean`,
lines 38–75).

| Formalism | Core Judgment Form | Loop Alignment Capability | Decidability / Completeness | Role in a Compiler Derivation Format |
| :--- | :--- | :--- | :--- | :--- |
| **Benton Relational Hoare Logic (RHL)** (POPL 2004, `doi:10.1145/964001.964003`) | $\vdash c_1 \sim c_2 : \Phi \Rightarrow \Psi$ over split states $(s_1, s_2)$ | Lockstep ($1$-to-$1$) and one-sided (`skipLeft`/`skipRight`) when loop condition is invariant on the stationary side | Sound; incomplete when loop conditions or iteration counts diverge between $c_1$ and $c_2$ | Core syntax-directed derivation skeleton for intra-block and CFG-preserving passes (CSE, DCE, constant folding, scheduling) |
| **Self-Composition & $2$-Product Programs** (Barthe, Crespo, Kunz FM 2011, `doi:10.1007/978-3-642-21437-0_17`) | Unary Hoare triple $\{P\}\, c_1 \times_\pi c_2 \,\{Q\}$ over woven product program under alignment policy $\pi$ | Expresses $(k_1, k_2)$-lockstep, loop peeling, unrolling, and fusion via explicit product CFG weaving | **Relatively complete** (in the sense of Cook 1978) for terminating/safety properties once a valid product alignment $\pi$ is chosen | Reduces cross-shape loop equivalence to unary invariant checking on a certificate-specified product CFG |
| **Cartesian Hoare Logic (CHL)** (Sousa & Dillig PLDI 2016, `doi:10.1145/2908080.2908092`) | $\langle \Phi \rangle\, \vec{c} \,\langle \Psi \rangle$ over $k$-tuples of executions | Prioritizes lockstep execution across longest common prefixes before falling back to unary execution | Relative completeness for $k$-safety; automated via CHC / Cartesian predicate abstraction | Useful for vectorization ($k=4, 8$ lanes) where $k$ scalar iterations are grouped into a single vector state |
| **Kleene Algebra with Tests (KAT)** (Kozen & Patron CL 2000, `doi:10.1007/3-540-44957-4_38`) | Equational implication $\Gamma \vdash p = q$ over Kleene star $p^*$, sequential composition $p \cdot q$, choice $p + q$, and Boolean tests $b$ | Handles loop peeling ($b p^* = (bp)^* b$), unswitching, dead-branch elimination, and tail-recursion elimination algebraically | **Decidable (PSPACE-complete)** and deductively complete over relational models of uninterpreted actions and tests | Fast decidable certificate rule for pure CFG restructuring (branch fusion, jump threading, loop peeling) when data actions are abstracted as uninterpreted symbols |

In `support/RelationalLogicsAndCompleteness.lean` (lines 51–75), we mechanize
the foundational equivalence between semantic RHL and unary Hoare logic over the
$2$-product command `ProductCmd`:

```lean
def SemanticRHL {S₁ S₂ : Type}
    (P : RelAssertion S₁ S₂) (c₁ : CmdRel S₁) (c₂ : CmdRel S₂) (Q : RelAssertion S₁ S₂) : Prop :=
  ∀ s₁ s₂ s₁' s₂', P s₁ s₂ → c₁ s₁ s₁' → c₂ s₂ s₂' → Q s₁' s₂'

theorem rhl_iff_product_hoare {S₁ S₂ : Type}
    (P : RelAssertion S₁ S₂) (c₁ : CmdRel S₁) (c₂ : CmdRel S₂) (Q : RelAssertion S₁ S₂) :
    SemanticRHL P c₁ c₂ Q ↔
      UnaryHoare (fun p => P p.1 p.2) (ProductCmd c₁ c₂) (fun p => Q p.1 p.2)
```

`#print axioms rhl_iff_product_hoare` confirms that this equivalence holds in
Lean `v4.34.1` with **zero axioms**.

### 2. Simulation Diagrams, Stuttering Measures, and Turning Forward Simulations into Backward Simulations

Basis: source + execution (`support/RelationalLogicsAndCompleteness.lean`,
lines 80–120) + CompCert (`common/Smallstep.v`, Leroy JAR 2009) + Anneal
(`anneal-mir-to-x86-compiler-vcgen-and-variable-step-refinement`).

Compiler passes rarely preserve a $1$-to-$1$ instruction step count: dead-code
elimination collapses $1$ source step into $0$ target steps ($1 \to 0$
stuttering), while instruction selection or ABI lowering expands $1$ source step
into $k \ge 1$ target steps ($1 \to k$ expansion).

1. **Variable-Step Forward Simulation with Stuttering Measure (`ForwardMeasureSim`):**
   A forward simulation between source transition system $(S_1, \to_1)$ and
   target $(S_2, \to_2)$ equips the state relation `matchStates : S₁ → S₂ → Prop`
   with a well-founded measure $\mu : S_1 \to \mathbb{N}$:
   $$\forall s_1, s_1', s_2.\; \text{matchStates}(s_1, s_2) \land (s_1 \to_1 s_1') \implies \exists s_2'.\; (s_2 \to_2^* s_2') \land \text{matchStates}(s_1', s_2') \land (s_2 = s_2' \implies \mu(s_1') < \mu(s_1)).$$
   Because $\mu(s_1)$ strictly decreases on every $0$-target-step transition
   ($s_2 = s_2'$), the compiler cannot silently translate a diverging source loop
   into a terminating empty target trace (`silent divergence elimination`).
2. **Turning Forward Simulations into Backward Simulations (`forward_to_backward_lockstep`):**
   Forward simulation proves that every source trace can be matched by *some*
   target trace. However, if the target machine were nondeterministic, the
   target could exhibit extra behaviors not present in the source. Therefore,
   sound compilation requires **backward simulation** (every target trace refines
   a source trace, or arises from source undefined behavior). Proving backward
   simulation directly for each pass is notoriously brittle because a single
   target instruction may correspond to the middle of a multi-instruction macro
   expansion. CompCert and Anneal solve this by proving **forward simulation**
   for every pass, composing the forward simulations transitively, and flipping
   the composed forward simulation into a backward simulation at the top level
   using two structural properties:
   - **Source Progress (`h_progress`):** Every safe non-halted source state
     $s_1$ has at least one valid transition $\exists s_1'.\, s_1 \to_1 s_1'$
     (or more generally in CompCert, **receptiveness** on external event traces).
   - **Target Determinism (`h_det`):** From a given target state $s_2$, any two
     transitions $s_2 \to_2 s_2'$ and $s_2 \to_2 s_2''$ reach the same state
     $s_2' = s_2''$ (modulo identical external event outputs).

   We mechanize this flip in `support/RelationalLogicsAndCompleteness.lean`
   (lines 103–120):

   ```lean
   theorem forward_to_backward_lockstep {S₁ S₂ : Type}
       (step₁ : S₁ → S₁ → Prop) (step₂ : S₂ → S₂ → Prop)
       (safe₁ : S₁ → Prop) (matchStates : S₁ → S₂ → Prop)
       (h_progress : ∀ s₁ s₂, matchStates s₁ s₂ → safe₁ s₁ → ∃ s₁', step₁ s₁ s₁')
       (h_fwd : ∀ s₁ s₁' s₂, matchStates s₁ s₂ → step₁ s₁ s₁' → ∃ s₂', step₂ s₂ s₂' ∧ matchStates s₁' s₂')
       (h_det : ∀ s₁ s₂ s₂' s₂'', matchStates s₁ s₂ → safe₁ s₁ → step₂ s₂ s₂' → step₂ s₂ s₂'' → s₂' = s₂'') :
       ∀ s₁ s₂ s₂',
         matchStates s₁ s₂ →
         safe₁ s₁ →
         step₂ s₂ s₂' →
         ∃ s₁', step₁ s₁ s₁' ∧ matchStates s₁' s₂'
   ```

   Again, `#print axioms forward_to_backward_lockstep` verifies **zero axioms**.

### 3. Memory Injections, Parametric/Open Simulations, and Step-Indexed Logical Relations (`Simuliris`, `ReLoC`)

Basis: source + execution (`support/RelationalLogicsAndCompleteness.lean`,
lines 125–164; `gitlab.mpi-sws.org/iris/simuliris` @ `e3abfcdc301f92250d4227fc03c00463bf57b982`;
Leroy & Blazy JAR 2008 `doi:10.1007/s10817-008-9099-1`; Song et al. POPL 2020
`doi:10.1145/3371113`; Frumin, Krebbers, & Birkedal LICS 2018
`doi:10.1145/3209108.3209174`).

1. **CompCert Memory Injections (`MemInj`):**
   A memory injection $f : \text{BlockId} \to \text{Option}(\text{BlockId} \times \mathbb{Z})$
   relates source memory $m_1$ and target memory $m_2$:
   - If $f(b_1) = \text{none}$, source block $b_1$ has been promoted to registers
     (`SROA` / `Mem2Reg`) or eliminated as dead stack storage; loads/stores to
     $b_1$ in $m_1$ have no physical footprint in $m_2$.
   - If $f(b_1) = \text{some}(b_2, \delta)$, every byte at $(b_1, \text{ofs})$ in
     $m_1$ injects into $(b_2, \text{ofs} + \delta)$ in $m_2$, with non-overlapping
     image intervals when $b_1 \ne b_1'$ map into the same merged stack frame
     block $b_2$ (as in `Mach` stack frame consolidation).
   - **Functorial Composition (`translatePtr_compose`):** In
     `support/RelationalLogicsAndCompleteness.lean` (lines 132–164), we define
     `MemInj.compose f g` by adding the offsets $\delta_1 + \delta_2$ (`some (b3, delta1 + delta2)`)
     and prove that pointer translation commutes with injection composition:
     `translatePtr (MemInj.compose f g) b1 ofs1 = (translatePtr f b1 ofs1).bind (fun (b2, ofs2) => translatePtr g b2 ofs2)`.
2. **Parametric and Open Simulations (Hur et al. POPL 2012, CompCertM POPL 2020):**
   Whole-program CompCert simulations assume a closed call graph. To support
   separate compilation and linking with foreign or assembly modules,
   **parametric simulations** (Hur, Dreyer, Neis, & Vafeiadis POPL 2012) and
   **CompCertM** (`Song et al. POPL 2020`) parameterize the simulation relation by
   an evolving Kripke world $w = (f, m_{\text{pub}}, m_{\text{priv}})$ tracking
   public (escaped) blocks versus private (unobservable local stack) blocks,
   governed by a rely-guarantee accessibility relation $w \sqsubseteq w'$
   (`inject_incr`: existing block mappings in $f$ are frozen, while new blocks
   may be allocated).
3. **Logical Relations, Step Indexing, `ReLoC`, and `Simuliris`:**
   - **ReLoC** (Frumin et al. LICS 2018) embeds a relational refinement judgment
     $e_1 \precsim e_2 : A$ inside higher-order step-indexed Iris separation
     logic using ghost state for the specification program $e_2$. Because vanilla
     Iris is indexed by $\mathbb{N}$ steps ($\triangleright$), ReLoC's adequacy
     theorem is **termination-insensitive**: a diverging target loop trivially
     consumes step-index fuel and satisfies $\triangleright$, so ReLoC alone
     cannot rule out a compiler pass that turns a terminating program into an
     infinite loop.
   - **Simuliris** (`simuliris/sim_iris/ simulation.v` at `e3abfcdc301f`)
     replaces ReLoC's step-indexed ghost-thread encoding with a **coinductive /
     stuttering-bijection simulation judgment (`sim_expr`)** layered over Iris
     resources (`sheap`), specifically engineered to prove soundness of Stacked
     Borrows and Tree Borrows optimizations (load-load forwarding, read-read
     reordering, dead-store elimination under `Unique`/`Frozen` protectors) while
     preserving **termination and divergence behavior**.

### 4. Equivalence of Loops Whose Shapes Differ (Correlation, Alignment, Unrolling, and Vectorization)

Basis: source + execution (`support/RelationalLogicsAndCompleteness.lean`,
lines 169–242) + Churchill et al. PLDI 2019 (`doi:10.1145/3314221.3314596`) +
Zaks & Pnueli FM 2008 / DDEC (Sharma, Schkufza, Churchill, Aiken OOPSLA 2013).

When an optimizer transforms loop structure, lockstep $(1, 1)$ CFG simulation
breaks. Three alignment regimes cover compiler loop optimizations:

1. **$(k_1, k_2)$-Counted Unrolling and Peeling (`unroll2_loop_alignment`):**
   A $k$-way unrolled loop executes $k$ scalar body steps per target back-edge
   for $\lfloor n / k \rfloor$ iterations, followed by an $(n \bmod k)$
   remainder epilogue. Rather than requiring the validator to discover a
   disjunctive invariant over $n \bmod k$, the certificate specifies the stride
   factor $k$ and epilogue split. In `support/RelationalLogicsAndCompleteness.lean`
   (lines 169–226), we formalize `runScalarLoop` and `runUnrolled2WithEpilogue`
   and prove `unroll2_loop_alignment`:
   $$\forall \text{step}, \text{base}, n, \text{acc}.\; \text{runUnrolled2WithEpilogue}(\text{step}, \text{base}, n, \text{acc}) = \text{runScalarLoop}(\text{step}, \text{base}, n, \text{acc}),$$
   using the additive loop decomposition lemma `runScalarLoop_add` (`m + k`
   iterations equal `m` iterations followed by `k` iterations from `base + m`).
2. **SIMD Lockstep Vectorization (`vectorize4_loop_alignment`):**
   When $w$ scalar loop iterations are packed into a $w$-lane SIMD register
   (`Vec4 α`), the simulation invariant states that the vector register holds the
   tuple of $w$ consecutive scalar array/accumulator elements, and each vector
   instruction (`simdMap4 f`) homomorphically advances all $w$ scalar lanes in a
   $(w, 1)$-step transition (`vectorize4_loop_alignment`, lines 230–242), modulo
   pre-verified no-alias/disjointness side conditions (`checkDisjoint64_sound`).
3. **Data-Driven Equivalence Checking (DDEC) & Semantic Program Alignment:**
   When two loops have data-dependent skips (e.g., filtering or sparse iteration),
   Churchill et al. (PLDI 2019) and Sharma et al. (OOPSLA 2013) construct a
   **state-dependent alignment predicate** $\mathcal{A}(s_1, s_2) \in \{\text{Left}, \text{Right}, \text{Both}\}$
   inferred from concrete execution traces (correlation matrices over loop
   counters and live variables). In a certificate-producing compiler, the
   optimizer (or an untrusted alignment oracle) emits $\mathcal{A}(s_1, s_2)$ and
   the relational invariant $\mathcal{I}(s_1, s_2)$ directly into the certificate;
   the trusted checker only verifies the three local inductiveness VCs:
   - $\mathcal{I}(s_1, s_2) \land \mathcal{A}(s_1, s_2) = \text{Left} \land (s_1 \to_1 s_1') \implies \mathcal{I}(s_1', s_2) \land \mu(s_1', s_2) < \mu(s_1, s_2)$,
   - $\mathcal{I}(s_1, s_2) \land \mathcal{A}(s_1, s_2) = \text{Right} \land (s_2 \to_2 s_2') \implies \mathcal{I}(s_1, s_2') \land \mu(s_1, s_2') < \mu(s_1, s_2)$,
   - $\mathcal{I}(s_1, s_2) \land \mathcal{A}(s_1, s_2) = \text{Both} \land (s_1 \to_1 s_1') \land (s_2 \to_2 s_2') \implies \mathcal{I}(s_1', s_2')$.

### 5. What "Complete Checking" Means for a Derivation Format and How It Is Stated

Basis: source + execution (`support/RelationalLogicsAndCompleteness.lean`,
lines 244–394).

A designer choosing the judgment forms of a proof-producing compiler must
separate three distinct theorems that are often conflated under the word
"completeness":

| Completeness Tier | Formal Theorem Statement | Attainable? | Why It Matters |
| :--- | :--- | :--- | :--- |
| **1. Semantic Equivalence Completeness** | $\forall c_1, c_2.\; (\llbracket c_1 \rrbracket = \llbracket c_2 \rrbracket) \implies \exists d.\; \text{check}(d, c_1, c_2) = \text{true}$ | **Impossible** for Turing-complete languages ($\Pi^0_2$-complete by Rice's theorem) | Explains why uninstrumented translation validators (Alive2, Value-Graph TV) must be incomplete on general loops |
| **2. Relative Deductive Completeness** | $\forall c_1, c_2, P, Q.\; \text{SemanticRHL}(P, c_1, c_2, Q) \implies \text{UnaryHoare}(P, c_1 \times c_2, Q)$ | **Yes** (`rhl_iff_product_hoare`) | Guarantees that the relational judgment form has no artificial structural blind spots once the product alignment schedule is given |
| **3. Check-Completeness (Syntax-Directed Certificate Decidability)** | $\forall d, c_1, c_2, \Delta.\; (\text{checkRelDeriv}(d, c_1, c_2, \Delta) = \text{true} \iff \text{ValidRelDeriv}(d, c_1, c_2, \Delta))$ | **Yes, in $O(\lvert d \rvert)$ time** (`checkRelDeriv_iff_valid`) | Guarantees that the boolean certificate checker never spuriously rejects a well-formed derivation tree $d$ emitted by an optimization pass |

In `support/RelationalLogicsAndCompleteness.lean` (lines 260–394), we construct
an explicit relational derivation format `RelDeriv` (`skipBoth`, `skipLeft`,
`skipRight`, `assignBoth`, `fuseAdd`, `seqBoth`), an inductive validity relation
`ValidRelDeriv d c1 c2 delta`, and a linear-time boolean checker `checkRelDeriv`.
Because `seqBoth d1 d2` synthesizes its intermediate offset split deterministically
via `inferDelta d1` and `inferDelta d2` (`validRelDeriv_inferDelta`), we prove
both semantic soundness (`validRelDeriv_implies_eval_eq`) and the exact
bidirectional **Check-Completeness theorem**:

```lean
theorem checkRelDeriv_iff_valid (d : RelDeriv) (c1 c2 : SimpleCmd) (delta : Int) :
    checkRelDeriv d c1 c2 delta = true ↔ ValidRelDeriv d c1 c2 delta
```

This bidirectional theorem yields a clear design rule for the compiler's
derivation format: **every rule with a cut or sequential/product split (`seqBoth`,
`cut`, `loopAlign`) must carry enough explicit intermediate boundary data (or a
deterministic synthesis function like `inferDelta`) so that `checkRelDeriv` is a
pure syntax-directed recursion without backtracking search**.

## Boundaries

- **Non-Terminating Source Loops and Step-Indexed Logics:** As noted in Finding
  3, step-indexed logical relations over $\mathbb{N}$ (`ReLoC`, standard Iris
  $\triangleright$) cannot prove divergence preservation without an explicit
  stuttering measure $\mu : S_1 \to \mathbb{N}$ (`ForwardMeasureSim`) or
  transfinite ordinal indexing. A compiler derivation format targeting total
  behavioral refinement (preserving both termination and silent divergence) must
  require a decreasing measure $\mu$ on every $1 \to 0$ source-stuttering or
  $\text{Left}$-only alignment step.
- **External Concurrency and Relaxed-Memory Simulators:** The forward-to-backward
  flip (`forward_to_backward_lockstep`) requires `TargetDeterministic` (modulo
  external event traces). For concurrent threads sharing relaxed-memory atomics,
  thread-local determinism holds only up to the trace of memory/synchronization
  events; flipping simulations across thread interleavings requires
  trace-receptive small-step semantics or DRF-SC reduction rather than closed
  state determinism.

## Evidence

- **Standalone Lean 4.34.1 Mechanization:**
  `support/RelationalLogicsAndCompleteness.lean` (`415` lines, verified with zero
  `sorry` and `#guard_msgs in #print axioms` on Lean `v4.34.1`, commit
  `5045d0056413266e57c625dcd7c365b10e377c52`) mechanizes:
  - `rhl_iff_product_hoare` (lines 66–75, `0` axioms),
  - `forward_to_backward_lockstep` (lines 103–120, `0` axioms),
  - `translatePtr_compose` (lines 148–164, `[propext]`),
  - `unroll2_loop_alignment` and `vectorize4_loop_alignment` (lines 215–242,
    `[propext, Classical.choice, Quot.sound]`),
  - `validRelDeriv_implies_eval_eq` and `checkRelDeriv_iff_valid` (lines 309–394,
    `[propext, Classical.choice, Quot.sound]`).
- **Primary Sources and Upstream Repositories:**
  - `gitlab.mpi-sws.org/iris/simuliris` at `e3abfcdc301f92250d4227fc03c00463bf57b982`
    (Gäher et al., POPL 2022, Simuliris stuttering simulation and Stacked/Tree
    Borrows separation logic).
  - `rocq-iris/iris` at `b3495ef9f0805b0dc7c1b1abbdc8cf473ede121b` and
    `leanprover-community/iris-lean` at `81bc35088ba67d465db008f5261a9b341eb6cf6c`.
  - `joshlf/anneal` at `beb778bb135474a67dc017c185d2753a60693d8c` and
    `24367bd1a8c784f2578535954f9915e24894a56f` (Anneal universal refinement
    kernel and variable-step simulation architecture).
  - Benton, POPL 2004 (`doi:10.1145/964001.964003`); Barthe, Crespo, & Kunz, FM
    2011 (`doi:10.1007/978-3-642-21437-0_17`); Sousa & Dillig, PLDI 2016
    (`doi:10.1145/2908080.2908092`); Kozen & Patron, CL 2000
    (`doi:10.1007/3-540-44957-4_38`); Leroy & Blazy, JAR 2008
    (`doi:10.1007/s10817-008-9099-1`); Song et al., POPL 2020
    (`doi:10.1145/3371113`); Frumin, Krebbers, & Birkedal, LICS 2018
    (`doi:10.1145/3209108.3209174`); Churchill et al., PLDI 2019
    (`doi:10.1145/3314221.3314596`).

## Revalidation

Run the standalone Lean `v4.34.1` mechanization via `anneal-lean-run` to check
all five theorems and their `#guard_msgs in #print axioms` assertions:

```bash
anneal-lean-run --mode file --concurrency 4 -- \
  lake env lean reports/relational-logics-simulation-techniques-and-completeness-for-compiler-derivations/support/RelationalLogicsAndCompleteness.lean
```
