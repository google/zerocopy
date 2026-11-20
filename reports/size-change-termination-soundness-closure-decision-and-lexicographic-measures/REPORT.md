# Size-change termination in Lean 4: soundness, exactness and decision of the closure criterion, and lexicographic projection measures

## Summary

This package mechanizes, in core Lean 4 (`v4.34.1`, no Mathlib), the size-change termination principle of Lee, Jones and Ben-Amram (POPL 2001) for a generic first-order toy model: a program has finitely many functions (`Fin nf`), every function has the same finite number `k` of parameter slots (`Fin k`), each call site is described by a size-change graph whose arcs say "callee argument `j` is `<` / `≤` caller parameter `i`", and argument values are natural numbers. All 15 results below are kernel-checked with only the axioms `propext`, `Classical.choice` and `Quot.sound`.

What a passed check licenses:

- **closure-iff-sct** (characterization). For finitely many functions and parameter slots, a program satisfies the closure criterion (every idempotent loop graph `G = G ; G` in the composition closure of its call-site graphs has a strict self-arc `(i, i, <)`) if and only if it is size-change terminating (every infinite path through its call sites, from any function, has an infinitely descending thread); finiteness of the functions is needed for the forward direction, finiteness of the parameter slots for both.
- **sct-sound-nat.** If a program (finitely many functions and parameter slots) is size-change terminating, no infinite call sequence with natural-number argument values is consistent with its graphs; well-founded (`Nat`) values are needed.
- **closure-criterion-sound.** If a program (finitely many functions and parameter slots) satisfies the closure criterion, no infinite call sequence with natural-number argument values is consistent with its graphs.
- **closure-criterion-sound-model.** If every call of a call relation on states (one of finitely many functions, natural-number values in finitely many parameter slots) is justified by a call-site graph that the call respects (`StepRespects`), and the graphs satisfy the closure criterion, the call relation has no infinite call sequence.
- **graphs-must-be-sound** (counterexample). A passed check licenses nothing about calls the graphs do not describe: `f(x) = f(x - 1)` with its `x > 0` guard forgotten (truncated subtraction, `0 - 1 = 0`) violates the accepted graph `x' < x` at `x = 0` and does not terminate.
- **no-run-length-bound** (counterexample). The criterion and even a decreasing lexicographic measure give no bound on run length in the abstraction: the Ackermann call structure has consistent finite runs of every length from the single start state `f(1, 0)`, because one call leaves an argument unconstrained.

Decision procedure and what rejection means:

- **closure-criterion-exact.** If some idempotent loop graph in the closure has no strict self-arc (finitely many parameter slots are needed; finiteness of the functions is harmless here), the graphs admit an infinite consistent call sequence with natural-number values; so the criterion is exactly "no consistent infinite `Nat` run" for the abstraction.
- **checker-correct** (characterization). The fixpoint checker `checkSCT` (closure by iteration with fuel `nf * nf * 3^(k*k) + 1`, then the idempotent-loop test) returns `true` if and only if the closure criterion holds.
- **nonstrict-self-arcs-insufficient** (counterexample). Requiring only a nonstrict self-arc on idempotent loop graphs is unsound: `f(x, y) = f(x, x - 1)` passes that weaker test and has an infinite consistent run.
- **generators-insufficient** (counterexample). Testing only the call-site graphs instead of the closure is unsound: the calls `f(x - 1, ?)` and `f(?, y - 1)` each pass, but their composite is the empty idempotent loop and an infinite consistent run exists.
- **composition-tracks-strictness** (counterexample). Composition must sequence labels exactly (`≤ ; < = <`, `< ; ≤ = <`, `≤ ; ≤ = ≤`): over-claiming `≤ ; ≤ = <` accepts `f(x) = f(x)`; forgetting either mixed case rejects a size-change-terminating mutual recursion.
- **sct-incomplete-for-termination** (counterexample). Rejection is not evidence of divergence: `f(x) = if x < 100 then f(x + 1) else 0` terminates, yet every one-function, one-slot abstraction whose graphs describe all of its calls on the raw argument `x` fails the criterion.

Lexicographic measures:

- **lex-implies-closure-criterion.** If some lexicographic tuple of single-parameter projections decreases on every call-site graph for all graph-consistent argument values, the program (finitely many functions and parameter slots) satisfies the closure criterion (so `checkSCT` accepts it).
- **sct-not-lex** (counterexample). The converse fails: the permuting call `f(x, y) = f(y, x - 1)` (for `x > 0`) passes the criterion and terminates, but no lexicographic tuple of single-parameter projections of any length decreases on its call.

Auxiliary lemma (not a headline result): **ramsey**, the infinite Ramsey theorem for pairs with finitely many colours, proved because the forward direction of closure-iff-sct is proved from it.

What these results do **not** show is listed first under **Boundaries** (non-claims per result), followed by escape hatches and refuted candidate statements. In particular: every result is about the size-change abstraction, and says something about a real program only through a separate proof that the program's calls respect the graphs.

*An agent relying on a result from this package must quote its plain-language claim and the relevant hypotheses and non-claims, not just its name or a paraphrase.*

## Applicability

**Model fidelity.** This is a toy model, kept generic on purpose. It is meant to capture the abstraction that size-change termination checkers work with: a finite set of first-order functions, one size-change graph per call site (or per branch of a call site), composition of graphs along call paths, and the idempotent-loop test on the composition closure. It does not model any particular language, evaluator or checker. Known gaps between the model and real systems:

- **Graphs are given, not derived.** No size analysis is modelled; whether a program's calls respect its graphs (`StepRespects`) is a separate obligation, and graphs describe calls only under the program's guards (truncated `Nat` subtraction `0 - 1 = 0` or `tail [] = []` break a strict arc exactly at the base case).
- **First-order calls only**, with a fixed finite set of functions and explicit call sites; higher-order calls are outside the model.
- **Unrooted:** every function is a possible entry point and the closure contains the composites of all call paths (as in Ben-Amram, LMCS 2010). Lee, Jones and Ben-Amram (POPL 2001) restrict call sequences and the closure to functions reachable from a designated initial function.
- **Uniform parameter count:** every function has `k` slots; a function with fewer parameters leaves slots without arcs. Such padding slots do not affect the closure, the criterion, size-change termination, consistent runs or `checkSCT`, but they do affect lexicographic projection measures.
- **Totalized composition:** `SCG.compWith` does not check `G.dst = H.src` (Lee, Jones and Ben-Amram define composition only for such pairs); the closure only composes composable pairs, and the loop guard `G.src = G.dst` of the criterion excludes non-loop graphs that are idempotent as label matrices.
- **Full closure, no subsumption:** `checkSCT` computes the whole closure; optimizations such as subsumption change what must be tested (Ben-Amram, LMCS 2010, Section 4.3) and are not covered.
- **Values are natural numbers;** another well-founded value domain would also need the compatibility laws `a < b ≤ c → a < c` and `a ≤ b < c → a < c`, which `RespectsIn` does not assume for a general type.
- **Evaluation order is not modelled:** connecting a functional program with nested calls to a call relation on evaluated argument states needs a separate call-by-value adequacy argument; under lazy evaluation an infinite call chain need not mean divergence.

**Infinite functions or parameters.** The module `Toy.SCT.Infinite` defines a generalized model `SCGInf F K` over arbitrary function and parameter types and proves that on `Fin nf` and `Fin k` it agrees with the package's model (`inClosure_iff_inClosureInf`, `closureCriterion_iff_closureCriterionInf`, `sizeChangeTerminating_iff_sizeChangeTerminatingInf`, `consistentRunIn_nat_iff_consistentRunInf`, `stepRespects_iff_stepRespectsInf`). It is used only to show that the finiteness built into `SCG nf k` is needed; no result is claimed for infinite systems.

**Real termination checkers.** The connection to real tools is a modeling bridge, not a theorem:

```text
Basis: derived (modeling bridge) + source
```

Agda's termination checker (Agda 2.9.0, module `Agda.Termination.Termination`) documents itself as based on Abel and Altenkirch's structural-recursion analysis and on Lee, Jones and Ben-Amram, with the criterion "In the completed call graph, each idempotent call-matrix from a function to itself must have a decreasing argument"; this has the shape of `ClosureCriterion` over richer arc labels. Isabelle/HOL's function package provides the termination method `size_change`, documented as "using a variation of the size-change principle, together with a graph decomposition technique", with internal `max`, `min` and multiset orders and SAT-based search. The ACL2 community book `books/acl2s/ccg/ccg.lisp` implements a calling-context-graph (CCG) termination analysis that runs a "size-change analysis" on the strongly connected components of its CCG (calling context graphs are due to Manolios and Vroon, CAV 2006). Lean 4's own termination inference is not size-change based: it searches lexicographic combinations of measures and builds definitions by well-founded recursion (source `src/Lean/Elab/PreDefinition/WF/GuessLex.lean` at `v4.34.1`). The reasoning for the bridge: each size-change-style checker computes call abstractions and tests idempotent loops of their composition closure, so the package's results transfer to such a checker only to the extent that (a) its abstraction is sound for the program's calls (the `StepRespects` obligation), (b) its arc labels, composition and loop test refine `Label.seq` and `ClosureCriterion`, and (c) its size measures are well founded. None of (a)–(c) was checked for any tool; the tools' richer labels (Agda's bounded increase and decrease with a termination depth, guardedness), rooting, call-graph decomposition and orders are not modelled. Exact correspondence with any tool is not claimed.

**Toolchain.** Lean `leanprover/lean4:v4.34.1` (commit `5045d0056413266e57c625dcd7c365b10e377c52`), core library only; no Mathlib, no Lake dependencies. The Lake project is in `lean/` (library `Toy`, modules `Toy.SCT.*`).

**Subjects.** `REPORT.json` lists the Lean toolchain (the checker of every theorem and the subject of the Lean-inference observations), the primary papers whose results are restated (Lee, Jones and Ben-Amram 2001; Ramsey 1930; Ben-Amram 2010; Ben-Amram and Lee 2009; Steila 2015), and the sources of the three other checkers used only for the modeling bridge above.

## Findings

### Core definitions

All definitions are in namespace `Toy.SCT` (modules `Toy/SCT/Graph.lean`, `Semantics.lean`, `Check.lean`). Each core definition has proved positive and negative examples in `Toy/SCT/Examples.lean` (for instance `seq_pos`/`seq_neg`, `comp_pos`/`comp_neg`, `inClosure_pos`/`inClosure_neg`, `respects_pos`/`respects_neg`, `isCallPath_pos`/`isCallPath_neg`, `hasInfDescThread_pos`/`hasInfDescThread_neg`, `lexLt_pos`/`lexLt_neg`, `checkSCT_pos`/`checkSCT_neg`, `closureCriterion_swapDec`/`not_closureCriterion_idLoop`).

```lean
inductive Label | absent | nonstrict | strict          -- no information, ≤, <
-- sequencing along a thread i → m → j: absent if either arc is absent, else strict if either is strict
def Label.seq : Label → Label → Label
structure SCG (nf k : Nat) where                       -- one call site from src to dst
  src : Fin nf
  dst : Fin nf
  lab : Fin k → Fin k → Label                          -- lab i j relates caller parameter i to callee argument j
structure Prog (nf k : Nat) where calls : List (SCG nf k)
-- composition: arc (i, j) is the join (max in absent < nonstrict < strict) over intermediate m of
-- sq (G.lab i m) (H.lab m j); src := G.src, dst := H.dst; total (does not check G.dst = H.src)
def SCG.compWith (sq : Label → Label → Label) (G H : SCG nf k) : SCG nf k
def SCG.comp (G H : SCG nf k) : SCG nf k := compWith Label.seq G H
inductive InClosureWith (sq) (P : Prog nf k) : SCG nf k → Prop
  | gen  : G ∈ P.calls → InClosureWith sq P G
  | comp : InClosureWith sq P G → InClosureWith sq P H → G.dst = H.src → InClosureWith sq P (G.compWith sq H)
abbrev InClosure P := InClosureWith Label.seq P
def SCG.HasStrictSelfArc (G) : Prop := ∃ i : Fin k, G.lab i i = Label.strict
def ClosureCriterion (P) : Prop := CriterionWith Label.seq P
  -- = ∀ G, InClosure P G → G.src = G.dst → G.comp G = G → G.HasStrictSelfArc
def RespectsIn {α} [LT α] [LE α] (G : SCG nf k) (u v : Fin k → α) : Prop :=
  ∀ i j, (G.lab i j = Label.strict → v j < u i) ∧ (G.lab i j = Label.nonstrict → v j ≤ u i)
abbrev Respects G (u v : Fin k → Nat) := RespectsIn G u v
def IsCallPath P (Gs : Nat → SCG nf k) : Prop := ∀ n, Gs n ∈ P.calls ∧ (Gs n).dst = (Gs (n + 1)).src
def HasInfDescThread (Gs) : Prop := ∃ (n0 : Nat) (p : Nat → Fin k),
  (∀ n, n0 ≤ n → (Gs n).lab (p n) (p (n + 1)) ≠ Label.absent) ∧
  (∀ N, ∃ n, N ≤ n ∧ n0 ≤ n ∧ (Gs n).lab (p n) (p (n + 1)) = Label.strict)
def SizeChangeTerminating P : Prop := ∀ Gs, IsCallPath P Gs → HasInfDescThread Gs
def ConsistentRunIn (α) [LT α] [LE α] P : Prop := ∃ fs vs Gs, ∀ n,
  Gs n ∈ P.calls ∧ (Gs n).src = fs n ∧ (Gs n).dst = fs (n + 1) ∧ RespectsIn (Gs n) (vs n) (vs (n + 1))
abbrev State (nf k) := Fin nf × (Fin k → Nat)
def StepRespects P (step : State nf k → State nf k → Prop) : Prop :=
  ∀ s t, step s t → ∃ G ∈ P.calls, G.src = s.1 ∧ G.dst = t.1 ∧ Respects G s.2 t.2
def Terminates (step : σ → σ → Prop) : Prop := ¬ ∃ s : Nat → σ, ∀ n, step (s n) (s (n + 1))
def runStep P : State nf k → State nf k → Prop :=        -- the most permissive model of P
  fun s t => ∃ G ∈ P.calls, G.src = s.1 ∧ G.dst = t.1 ∧ Respects G s.2 t.2
```

Intent: `ClosureCriterion` is the test of Lee, Jones and Ben-Amram (Theorem 4) on the unrooted closure; `SizeChangeTerminating` is their Definition 11 in the unrooted form of Ben-Amram (LMCS 2010); `ConsistentRunIn Nat` is an infinite call sequence of the abstraction itself, with natural-number values respecting every graph used; `StepRespects` is the obligation that the graphs are sound for a semantic call relation; `checkSCT` is a reference implementation of the graph-based algorithm. Concrete arc lists are written with `arcsG src dst [(i, j, label), ...]` (unlisted arcs are `absent`; first match wins). Fixture programs (module `Toy/SCT/Fixtures.lean`) are quoted with the results that use them.

**Depth convention.** Depth labels are marginal: they measure the argument needed given the earlier results of the package.

### What a passed check licenses

#### `closure-iff-sct`

**Claim.** A program (finitely many functions, finitely many parameter slots) satisfies the closure criterion (every idempotent loop graph G = G ; G in the composition closure of its call-site graphs has a strict self-arc) if and only if it is size-change terminating (every infinite path through its call sites, from any function, has an infinitely descending thread).

**Tier:** T0. Theorem 4 of Lee, Jones and Ben-Amram (POPL 2001) in the unrooted form (Ben-Amram, LMCS 2010; Ben-Amram and Lee, LMCS 2009, Theorem 2), restated in this vocabulary; mechanized before in Isabelle/HOL (Krauss, CADE 2007; Wright, Cohen, Rowe and Popescu, ITP 2026) and in PVS (Munoz et al., ITP 2021).

**Kind:** characterization. **Lean:** `Toy.SCT.sizeChangeTerminating_of_closureCriterion`, `Toy.SCT.closureCriterion_of_sizeChangeTerminating`

```lean
theorem Toy.SCT.sizeChangeTerminating_of_closureCriterion {nf k : Nat} (P : Prog nf k)
    (h : ClosureCriterion P) : SizeChangeTerminating P
theorem Toy.SCT.closureCriterion_of_sizeChangeTerminating {nf k : Nat} (P : Prog nf k)
    (h : SizeChangeTerminating P) : ClosureCriterion P

-- unfolded
ClosureCriterion P =
  ∀ G : SCG nf k, InClosureWith Label.seq P G → G.src = G.dst →
    G.compWith Label.seq G = G → ∃ i : Fin k, G.lab i i = Label.strict
SizeChangeTerminating P =
  ∀ Gs : Nat → SCG nf k, (∀ n, Gs n ∈ P.calls ∧ (Gs n).dst = (Gs (n + 1)).src) →
    ∃ (n0 : Nat) (p : Nat → Fin k),
      (∀ n, n0 ≤ n → (Gs n).lab (p n) (p (n + 1)) ≠ Label.absent) ∧
      (∀ N, ∃ n, N ≤ n ∧ n0 ≤ n ∧ (Gs n).lab (p n) (p (n + 1)) = Label.strict)
```

**Hypothesis ledger.** Forward direction (`ClosureCriterion P → SizeChangeTerminating P`).

| Hypothesis | Why it is needed | Tightness |
| :--- | :--- | :--- |
| h : ClosureCriterion P - component: the test ranges over the whole composition closure, not just the call-site graphs (forward direction) | A loop that alternates two calls is only visible in a composite graph. | tight: counterexample `alt_generatorCriterion_counterexample` |
| h : ClosureCriterion P - component: the self-arc must be strict (forward direction) | A nonstrict self-arc only says a value does not grow; it never forces descent. | tight: counterexample `stall_weakSelfArcCriterion_counterexample` |
| h : ClosureCriterion P - component: composition does not over-claim strictness, <= ; <= = <= (forward direction) | Over-claiming strictness manufactures a strict self-arc that no thread justifies. | tight: counterexample `overStrict_composition_counterexample` |
| finitely many functions (built into SCG nf k as Fin nf; needed for the forward direction only) | Forward direction (ClosureCriterion P -> SizeChangeTerminating P): with infinitely many functions a call chain f_0 -> f_1 -> ... has no loop graphs at all, so the criterion holds vacuously without size-change termination (generalized model SCGInf). Not needed for the converse, which goes through closure-criterion-exact; that proof uses finiteness of the parameter slots only. The generalized model agrees with this one on finite types (closureCriterion_iff_closureCriterionInf, sizeChangeTerminating_iff_sizeChangeTerminatingInf, consistentRunIn_nat_iff_consistentRunInf), so the counterexample varies only the finiteness assumption. | tight: counterexample `infinite_functions_counterexample` |
| finitely many parameter slots (built into SCG nf k as Fin k; needed for both directions) | With infinitely many parameters the forward direction fails (shift graph: no idempotent graph, no descending thread) and so does the converse (a dense strict order gives an idempotent loop without self-arcs, yet every path has a descending thread) (generalized model SCGInf). The generalized model agrees with this one on finite types (closureCriterion_iff_closureCriterionInf, sizeChangeTerminating_iff_sizeChangeTerminatingInf, consistentRunIn_nat_iff_consistentRunInf), so the counterexample varies only the finiteness assumption. | tight: counterexample `infinite_params_soundness_counterexample`, `infinite_params_converse_exactness_counterexample` |

**Hypothesis ledger.** Converse direction (`SizeChangeTerminating P → ClosureCriterion P`).

| Hypothesis | Why it is needed | Tightness |
| :--- | :--- | :--- |
| ClosureCriterion P - component: composition keeps mixed strictness, <= ; < = < and < ; <= = < (converse direction) | Forgetting either mixed case turns a strict two-call cycle into a nonstrict idempotent loop. | tight: counterexample `forget_composition_rejects_mutProg` |
| ClosureCriterion P - component: only loop graphs G.src = G.dst are tested (converse direction) | Composition is total, so a non-loop graph can be idempotent as a label matrix; testing it rejects a non-recursive program. | tight: counterexample `loop_guard_needed_for_converse` |
| ClosureCriterion P - component: only idempotent loop graphs are tested (converse direction) | A size-change-terminating program can have non-idempotent loop graphs without self-arcs. | tight: counterexample `idempotence_needed_for_converse` |
| h : SizeChangeTerminating P (premise of the converse direction) | Premise of the converse; without it the criterion can fail. | tight: counterexample `idLoop_decLoop_contrast` |
| finitely many parameter slots (built into SCG nf k as Fin k; needed for both directions) | With infinitely many parameters the forward direction fails (shift graph: no idempotent graph, no descending thread) and so does the converse (a dense strict order gives an idempotent loop without self-arcs, yet every path has a descending thread) (generalized model SCGInf). The generalized model agrees with this one on finite types (closureCriterion_iff_closureCriterionInf, sizeChangeTerminating_iff_sizeChangeTerminatingInf, consistentRunIn_nat_iff_consistentRunInf), so the counterexample varies only the finiteness assumption. | tight: counterexample `infinite_params_soundness_counterexample`, `infinite_params_converse_exactness_counterexample` |

**Depth:** substantive. Forward direction (Toy/SCT/Soundness.lean): colour each pair of positions of an infinite call path by the composite of the graphs between them (colours range over the finite list of all graphs, Toy/SCT/Enum.lean), apply Ramsey's theorem for pairs (card ramsey) to get an idempotent loop graph of the closure, and glue the threads given by its strict self-arc into an infinitely descending thread. Converse: via closure-criterion-exact and sct-sound-nat. Both directions rest on the thread semantics of composition (Toy/SCT/Threads.lean).

**Non-vacuity witness:** The permuting call f(x, y) = f(y, x - 1) (for x > 0) satisfies the criterion and is size-change terminating (its path gSwap, gSwap, ... has the thread x, y, x, y, ...); so does f(x) = f(x - 1). (Lean: `closure_iff_sct_nonvacuous`)

**Prior art:** [P1], [P2], [P3], [P4], [P5], [P6], [P7], [P8], [P9] (records under Evidence).

**Design question:** What exactly does a passed size-change (closure-criterion) check license about a recursive definition, and what does it not license?

**Non-claims:** see Boundaries, `closure-iff-sct`.

```text
Basis: execution (Lean kernel check)
```

```text
Basis: derived (modeling bridge)
```

Size-change checkers such as Agda's termination checker test idempotent loops of a composition closure of call abstractions (see Applicability); this theorem says that, for such a test with exactly the package's labels and composition, acceptance means every infinite call path has an infinitely descending thread, and conversely. Whether a given tool's labels, composition and loop test refine `Label.seq` and `ClosureCriterion` is not checked here.

#### `sct-sound-nat`

**Claim.** If every infinite path through a program's call sites has an infinitely descending thread, then there is no infinite call sequence with natural-number argument values consistent with the program's size-change graphs. The kernel-checked theorem covers only programs with finitely many functions and finitely many parameter slots (Fin nf, Fin k): its statement quantifies over P : Prog nf k.

**Tier:** T0. Theorem 1 of Lee, Jones and Ben-Amram and Lemma 3.4 of Ben-Amram (LMCS 2010), restated over Nat.

**Kind:** theorem. **Lean:** `Toy.SCT.no_consistent_nat_run_of_sizeChangeTerminating`

```lean
theorem Toy.SCT.no_consistent_nat_run_of_sizeChangeTerminating {nf k : Nat} (P : Prog nf k)
    (h : SizeChangeTerminating P) : ¬ ConsistentRunIn Nat P

-- unfolded
ConsistentRunIn Nat P =
  ∃ (fs : Nat → Fin nf) (vs : Nat → Fin k → Nat) (Gs : Nat → SCG nf k),
    ∀ n, Gs n ∈ P.calls ∧ (Gs n).src = fs n ∧ (Gs n).dst = fs (n + 1) ∧
      ∀ i j, ((Gs n).lab i j = Label.strict → vs (n + 1) j < vs n i) ∧
             ((Gs n).lab i j = Label.nonstrict → vs (n + 1) j ≤ vs n i)
```

**Hypothesis ledger.**

| Hypothesis | Why it is needed | Tightness |
| :--- | :--- | :--- |
| h : SizeChangeTerminating P | Supplies the infinitely descending thread along the run's call path. | tight: counterexample `idLoop_decLoop_contrast` |
| values are natural numbers (ConsistentRunIn Nat) | Infinite descent is impossible only in a well-founded order; over Int a strictly decreasing argument runs forever. | tight: counterexample `decLoop_closureCriterion_consistent_int_run` |

**Depth:** shallow. Follow the thread's values along the run: they never increase and decrease infinitely often, contradicting well-foundedness of Nat.

**Non-vacuity witness:** f(x, y) = f(y, x - 1) (for x > 0) is size-change terminating. (Lean: `sct_sound_nat_nonvacuous`)

**Prior art:** [P1], [P3] (records under Evidence).

**Design question:** What exactly does a passed size-change (closure-criterion) check license about a recursive definition, and what does it not license?

**Non-claims:** see Boundaries, `sct-sound-nat`.

```text
Basis: execution (Lean kernel check)
```

#### `closure-criterion-sound`

**Claim.** If every idempotent loop graph G = G ; G in the composition closure of a program's size-change graphs (finitely many functions and parameter slots) has a strict self-arc (i, i, <), then there is no infinite call sequence with natural-number argument values consistent with the graphs.

**Tier:** T0. The closure-criterion soundness of Lee, Jones and Ben-Amram (Theorem 4 combined with Theorem 1), restated over Nat.

**Kind:** theorem. **Lean:** `Toy.SCT.no_consistent_nat_run_of_closureCriterion`

```lean
theorem Toy.SCT.no_consistent_nat_run_of_closureCriterion {nf k : Nat} (P : Prog nf k)
    (h : ClosureCriterion P) : ¬ ConsistentRunIn Nat P
-- ClosureCriterion and ConsistentRunIn Nat as unfolded above
```

**Hypothesis ledger.**

| Hypothesis | Why it is needed | Tightness |
| :--- | :--- | :--- |
| h : ClosureCriterion P — component: the test ranges over the whole composition closure, not just the call-site graphs | A loop that alternates two calls is only visible in a composite graph. | tight: counterexample `alt_generatorCriterion_counterexample` |
| h : ClosureCriterion P — component: the self-arc must be strict | A nonstrict self-arc only says a value does not grow; it never forces descent. | tight: counterexample `stall_weakSelfArcCriterion_counterexample` |
| h : ClosureCriterion P - component: composition does not over-claim strictness, <= ; <= = <= | Over-claiming strictness (<= ; <= = <) manufactures a strict self-arc that no thread justifies. | tight: counterexample `overStrict_composition_counterexample` |
| values are natural numbers (ConsistentRunIn Nat) | Infinite descent is impossible only in a well-founded order; over Int a strictly decreasing argument runs forever. | tight: counterexample `decLoop_closureCriterion_consistent_int_run` |
| finitely many functions (built into SCG nf k as Fin nf) | With infinitely many functions the criterion can hold vacuously while an infinite consistent run exists (generalized model SCGInf). The generalized model agrees with this one on finite types (closureCriterion_iff_closureCriterionInf, sizeChangeTerminating_iff_sizeChangeTerminatingInf, consistentRunIn_nat_iff_consistentRunInf), so the counterexample varies only the finiteness assumption. | tight: counterexample `infinite_functions_counterexample` |
| finitely many parameter slots (built into SCG nf k as Fin k) | With infinitely many parameters the criterion can hold vacuously while an infinite consistent run exists (generalized model SCGInf). The generalized model agrees with this one on finite types (closureCriterion_iff_closureCriterionInf, sizeChangeTerminating_iff_sizeChangeTerminatingInf, consistentRunIn_nat_iff_consistentRunInf), so the counterexample varies only the finiteness assumption. | tight: counterexample `infinite_params_soundness_counterexample` |

**Depth:** shallow. One line given closure-iff-sct (forward direction) and sct-sound-nat. The substance (Ramsey's theorem and the thread semantics of composition) is in closure-iff-sct. (Depth labels in this package are marginal: they measure the argument needed given the earlier results of the package.)

**Non-vacuity witness:** The criterion holds for the permuting call f(x, y) = f(y, x - 1) (for x > 0), for two mutually recursive one-parameter functions (f0(x) calls f1(x - 1) for x > 0, f1(y) calls f0(y)), and for the Ackermann call structure. (Lean: `closure_criterion_sound_nonvacuous`)

**Prior art:** [P1], [P2], [P3], [P6] (records under Evidence).

**Design question:** What exactly does a passed size-change (closure-criterion) check license about a recursive definition, and what does it not license?

**Non-claims:** see Boundaries, `closure-criterion-sound`.

```text
Basis: execution (Lean kernel check)
```

#### `closure-criterion-sound-model`

**Claim.** If every call made by a call relation step on states (one of finitely many functions, together with a vector of natural-number argument values over finitely many parameter slots) is justified by some call-site graph of P with matching endpoints that the call respects, and P satisfies the closure criterion, then step has no infinite call sequence.

**Tier:** T0. Theorem 1 of Lee, Jones and Ben-Amram (safe graphs over well-founded data) combined with their Theorem 4, for an arbitrary call relation on Nat-valued states.

**Kind:** theorem. **Lean:** `Toy.SCT.terminates_of_stepRespects_of_closureCriterion`

```lean
theorem Toy.SCT.terminates_of_stepRespects_of_closureCriterion {nf k : Nat} (P : Prog nf k)
    (step : State nf k → State nf k → Prop) (hstep : StepRespects P step)
    (h : ClosureCriterion P) : Terminates step

-- unfolded
State nf k = Fin nf × (Fin k → Nat)
StepRespects P step =
  ∀ s t, step s t → ∃ G ∈ P.calls, G.src = s.1 ∧ G.dst = t.1 ∧
    ∀ i j, (G.lab i j = Label.strict → t.2 j < s.2 i) ∧ (G.lab i j = Label.nonstrict → t.2 j ≤ s.2 i)
Terminates step = ¬ ∃ s : Nat → State nf k, ∀ n, step (s n) (s (n + 1))
```

**Hypothesis ledger.**

| Hypothesis | Why it is needed | Tightness |
| :--- | :--- | :--- |
| hstep : StepRespects P step (the graphs are sound for the real calls) | Connects the real call relation to the graphs; without it the graphs say nothing about step. | tight: counterexample `misfit_graphs_counterexample` |
| h : ClosureCriterion P | The abstraction must exclude infinite consistent runs. | tight: counterexample `idLoop_runStep_counterexample` |
| argument values are natural numbers (State nf k := Fin nf x (Fin k -> Nat)) | Over integer states the model x -> x - 1 respects x' < x on every call and the criterion holds, yet it does not terminate. | tight: counterexample `decLoop_int_model_counterexample` |
| finitely many functions (State nf k := Fin nf x (Fin k -> Nat) uses Fin nf) | With infinitely many functions the call chain f_0 -> f_1 -> ... has no loop graphs, so the criterion holds vacuously, yet it has an infinite consistent Nat run (infinite_functions_counterexample, graph-level form). Model-level form, proved in Lean: infinite_functions_model_counterexample (the most permissive model respects the graphs, the criterion holds, and the model does not terminate). The generalized model agrees with StepRespects on finite types (stepRespects_iff_stepRespectsInf, closureCriterion_iff_closureCriterionInf). | tight: counterexample `infinite_functions_counterexample` |
| finitely many parameter slots (State nf k := Fin nf x (Fin k -> Nat) uses Fin k) | With infinitely many parameters the single shift call (parameter i passed, not larger, to position i + 1) has no idempotent closure graph, so the criterion holds vacuously, yet it has an infinite consistent Nat run (infinite_params_soundness_counterexample, graph-level form). Model-level form, proved in Lean: infinite_params_model_counterexample. The generalized model agrees with StepRespects on finite types (stepRespects_iff_stepRespectsInf, closureCriterion_iff_closureCriterionInf). | tight: counterexample `infinite_params_soundness_counterexample` |

**Depth:** shallow. An infinite step sequence yields an infinite consistent run (choose a justifying graph per step); then apply closure-criterion-sound. (Depth labels in this package are marginal: they measure the argument needed given the earlier results of the package.)

**Non-vacuity witness:** The model of f(x, y) = if x = 0 then 0 else f(y, x - 1) respects the graph x' <= y, y' < x, which satisfies the criterion. (Lean: `closure_criterion_sound_model_nonvacuous`)

**Prior art:** [P1], [P3], [P8] (records under Evidence).

**Design question:** What exactly does a passed size-change (closure-criterion) check license about a recursive definition, and what does it not license?

**Non-claims:** see Boundaries, `closure-criterion-sound-model`.

```text
Basis: execution (Lean kernel check)
```

```text
Basis: derived (modeling bridge)
```

For a real first-order program, take `step` to be its call relation on states made of the current function and the `Nat` sizes of its evaluated arguments. The theorem then reduces termination of the program to (i) `StepRespects`, i.e. soundness of the graphs for every real call under its guards, and (ii) the closure criterion. Obtaining such a `step` from a program with nested calls needs a call-by-value adequacy argument (Lee, Jones and Ben-Amram, Lemmas 2 and 3) that is not formalized.

#### `graphs-must-be-sound`

**Claim.** The graph x' < x satisfies the closure criterion and checkSCT accepts it, but the model of f(x) = f(x - 1) with the base-case guard forgotten (truncated subtraction, so 0 calls 0 - 1 = 0) respects that graph on every call with x > 0, fails it on the call from 0, and does not terminate; likewise the model of f(x) = f(x).

**Tier:** T0. Immediate; corresponds to the safety requirement on graphs in Theorem 1 of Lee, Jones and Ben-Amram.

**Kind:** counterexample. **Lean:** `Toy.SCT.misfit_graphs_counterexample`

```lean
theorem Toy.SCT.misfit_graphs_counterexample :
    ClosureCriterion decLoop ∧ checkSCT decLoop = true ∧
    (∀ s t, unguardedDecStep s t → 0 < s.2 0 → Respects gDec s.2 t.2) ∧
    ¬ StepRespects decLoop unguardedDecStep ∧ ¬ Terminates unguardedDecStep ∧
    ¬ StepRespects decLoop idStep ∧ ¬ Terminates idStep

-- fixtures
gDec    : SCG 1 1 := arcsG f0 f0 [(0, 0, .strict)]          -- x' < x
decLoop : Prog 1 1 := ⟨[gDec]⟩
unguardedDecStep s t = (t.1 = s.1 ∧ t.2 0 = s.2 0 - 1)       -- truncated subtraction, no guard
idStep s t = (t = s)                                         -- f(x) = f(x)
```

**Hypothesis ledger.** None: this is a closed statement about concrete programs (all of its parts are proved for the named instances).

**Depth:** definitional. The call 0 -> 0 violates x' < x; the constant run at 0 is infinite.

**Non-vacuity witness:** Concrete program decLoop and models unguardedDecStep and idStep. (Lean: `misfit_graphs_counterexample`)

**Prior art:** [P1] (records under Evidence).

**Design question:** What exactly does a passed size-change (closure-criterion) check license about a recursive definition, and what does it not license?

**Non-claims:** see Boundaries, `graphs-must-be-sound`.

```text
Basis: execution (Lean kernel check)
```

#### `no-run-length-bound`

**Claim.** In the abstraction, the Ackermann call structure (calls f(x - 1, ?) and f(x, y - 1)) satisfies the closure criterion and has the decreasing lexicographic measure (x, y), yet from the single start state f(1, 0) there are consistent finite runs of every length N, because the call f(x - 1, ?) leaves the second argument unconstrained.

**Tier:** T1. Folklore that termination certificates carry no complexity bound; Ben-Amram (2002) shows size-change-terminating programs compute exactly the multiply-recursive functions. The concrete statement here is about the nondeterministic abstraction.

**Kind:** counterexample. **Lean:** `Toy.SCT.ackProg_unbounded_finite_runs`

```lean
theorem Toy.SCT.ackProg_unbounded_finite_runs :
    ClosureCriterion ackProg ∧ LexProjDecreases ackProg ackOrd ∧
    ∀ N : Nat, FiniteRunFrom ackProg f0 (vec2 1 0) N

-- fixtures and definitions
gX      : SCG 1 2 := arcsG f0 f0 [(0, 0, .strict)]                      -- f(x - 1, ?)
gKeepX  : SCG 1 2 := arcsG f0 f0 [(0, 0, .nonstrict), (1, 1, .strict)]  -- f(x, y - 1)
ackProg : Prog 1 2 := ⟨[gX, gKeepX]⟩
ackOrd  := fun _ l => l                                                 -- measure (x, y)
FiniteRunFrom P f u len =
  ∃ (fs : Nat → Fin nf) (vs : Nat → Fin k → Nat) (Gs : Nat → SCG nf k),
    fs 0 = f ∧ vs 0 = u ∧
    ∀ n, n < len → Gs n ∈ P.calls ∧ (Gs n).src = fs n ∧ (Gs n).dst = fs (n + 1) ∧
      Respects (Gs n) (vs n) (vs (n + 1))
```

**Hypothesis ledger.** None: this is a closed statement about concrete programs (all of its parts are proved for the named instances).

**Depth:** shallow. For N >= 1: first the call f(0, N - 1) (allowed because gX leaves y unconstrained), then N - 1 calls decreasing y to 0; for N = 0 the empty run.

**Non-vacuity witness:** Concrete program ackProg from start (1, 0). (Lean: `ackProg_unbounded_finite_runs`)

**Positive control:** For f(x) = f(x - 1) (program decLoop, single graph x' < x, which leaves no callee argument unconstrained), every consistent finite run from argument u 0 has at most u 0 steps (FiniteRunFrom decLoop f0 u N -> N <= u 0), so the run-length bound that fails for ackProg holds for this program. (Lean: `no_run_length_bound_positive_control`)

**Prior art:** [P10], [P1] (records under Evidence).

**Design question:** What exactly does a passed size-change (closure-criterion) check license about a recursive definition, and what does it not license?

**Non-claims:** see Boundaries, `no-run-length-bound`.

```text
Basis: execution (Lean kernel check)
```

### Decision procedure and what rejection means

#### `closure-criterion-exact`

**Claim.** If some idempotent loop graph in the composition closure of a program's size-change graphs (finitely many functions and parameter slots) has no strict self-arc, then there is an infinite call sequence with natural-number argument values consistent with the program's graphs.

**Tier:** T0. Known: Ben-Amram and Lee (LMCS 2009, Theorems 1 and 2, the 'only if' direction credited to Lee, TOPLAS 2009) state that the transition system T_G of a set of size-change graphs over any well-ordered value set, Nat included, terminates iff every idempotent graph of the closure has a strict self-arc; this card is the 'only if' half for Nat, restated in this vocabulary. Ben-Amram (LMCS 2010, Lemma 3.7 and Theorem 3.8) proves completeness for general monotonicity constraints over a constructed well-ordered set.

**Kind:** theorem. **Lean:** `Toy.SCT.consistent_nat_run_of_not_closureCriterion`

```lean
theorem Toy.SCT.consistent_nat_run_of_not_closureCriterion {nf k : Nat} (P : Prog nf k)
    (h : ¬ ClosureCriterion P) : ConsistentRunIn Nat P
-- ClosureCriterion and ConsistentRunIn Nat as unfolded under closure-iff-sct and sct-sound-nat
```

**Hypothesis ledger.**

| Hypothesis | Why it is needed | Tightness |
| :--- | :--- | :--- |
| h : ¬ ClosureCriterion P | Premise; programs satisfying the criterion have no consistent run (card closure-criterion-sound). | tight: counterexample `idLoop_decLoop_contrast` |
| finitely many parameter slots (built into SCG nf k as Fin k) | With infinitely many parameters an idempotent loop graph without self-arcs can coexist with the absence of any consistent Nat run (dense strict order, generalized model SCGInf). | tight: counterexample `infinite_params_converse_exactness_counterexample` |
| finitely many functions (built into SCG nf k as Fin nf) | Not needed by the construction: the run only visits the functions of one finite factor path of the failing graph, and the Lean proof uses finiteness of the parameter slots only. | harmless |

**Depth:** substantive. Toy/SCT/Exactness.lean: write the failing graph G as the composite of a call-site path F 0, ..., F (m - 1) (Toy/SCT/Threads.lean) and repeat that path forever. Because G = G ; G has no strict self-arc, its strict arcs form a strict partial order, ranked by the number hc q of strict arcs out of q. Block boundaries get the values (m + 1) * hc q + m and positions inside a block get the least values respecting the remaining arcs of the block (backward maximum over arcs); every arc of every step is respected.

**Non-vacuity witness:** The criterion fails for f(x, y) = f(x, x - 1) and for the alternating program with calls f(x - 1, ?) and f(?, y - 1). (Lean: `closure_criterion_exact_nonvacuous`)

**Prior art:** [P6], [P11], [P3], [P1] (records under Evidence).

**Design question:** Can the closure criterion be decided by a simple fixpoint computation whose acceptance is trustworthy, and what does rejection mean?

**Non-claims:** see Boundaries, `closure-criterion-exact`.

```text
Basis: execution (Lean kernel check)
```

#### `checker-correct`

**Claim.** checkSCT P (compute the composition closure of the call-site graphs by fixpoint iteration with fuel nf * nf * 3^(k*k) + 1, then test every idempotent loop graph for a strict self-arc) returns true if and only if P satisfies the closure criterion.

**Tier:** T0. The graph-based algorithm of Lee, Jones and Ben-Amram (Section 3.2) made precise as a fuel-bounded fixpoint iteration.

**Kind:** characterization. **Lean:** `Toy.SCT.closureCriterion_of_checkSCT_eq_true`, `Toy.SCT.checkSCT_eq_true_of_closureCriterion`

```lean
theorem Toy.SCT.closureCriterion_of_checkSCT_eq_true {nf k : Nat} (P : Prog nf k)
    (h : checkSCT P = true) : ClosureCriterion P
theorem Toy.SCT.checkSCT_eq_true_of_closureCriterion {nf k : Nat} (P : Prog nf k)
    (h : ClosureCriterion P) : checkSCT P = true

-- the checker
def checkSCT (P : Prog nf k) : Bool :=
  match closureIter (closureFuel nf k) (dedupGraphs P.calls) with
  | none   => false
  | some S => S.all idemTest
closureFuel nf k = nf * nf * 3 ^ (k * k) + 1
closureIter (n + 1) S = if every graph of closureStep S is in S then some S
                        else closureIter n (closureStep S);   closureIter 0 S = none
closureStep S = S extended by every composite G.comp H (G, H ∈ S, G.dst = H.src) not yet present
idemTest G = !(G.src = G.dst && G.comp G = G) || G.HasStrictSelfArc
```

**Hypothesis ledger.**

| Hypothesis | Why it is needed | Tightness |
| :--- | :--- | :--- |
| h : checkSCT P = true (soundness direction) / h : ClosureCriterion P (completeness direction) | The premise of each direction. | tight: counterexample `checker_premise_contrast` |

**Depth:** substantive. Soundness is shallow (a fixpoint list containing the generators and closed under composition contains the closure). Completeness needs a counting argument (Toy/SCT/CheckCorrect.lean): every list produced is duplicate-free and consists of closure graphs, each non-final iteration step adds a new graph, and a duplicate-free list of graphs has at most nf * nf * 3^(k*k) elements (explicit enumeration, Toy/SCT/Enum.lean).

**Non-vacuity witness:** checkSCT accepts the permuting call, which satisfies the criterion. (Lean: `checker_correct_nonvacuous`)

**Prior art:** [P1], [P2], [P3], [P8] (records under Evidence).

**Design question:** Can the closure criterion be decided by a simple fixpoint computation whose acceptance is trustworthy, and what does rejection mean?

**Non-claims:** see Boundaries, `checker-correct`.

```text
Basis: execution (Lean kernel check)
```

```text
Basis: derived (modeling bridge)
```

`checkSCT` is a specification-level reference checker (fuel and list scans are impractical beyond tiny closures). A production checker that computes the same closure and test agrees with it; one that prunes the closure (for example by subsumption) is not covered.

#### `nonstrict-self-arcs-insufficient`

**Claim.** For f(x, y) = f(x, x - 1) (for x > 0), every idempotent loop graph in the closure has a self-arc, but only a nonstrict one (the graph also has a strict arc x -> y'); the closure criterion fails, the program is not size-change terminating, it has an infinite consistent Nat run, and its most permissive model does not terminate.

**Tier:** T0. Immediate from the definitions; the strictness requirement is part of Theorem 4 of Lee, Jones and Ben-Amram.

**Kind:** counterexample. **Lean:** `Toy.SCT.stall_weakSelfArcCriterion_counterexample`

```lean
theorem Toy.SCT.stall_weakSelfArcCriterion_counterexample :
    WeakSelfArcCriterion stallProg ∧ ¬ ClosureCriterion stallProg ∧
    ¬ SizeChangeTerminating stallProg ∧ ConsistentRunIn Nat stallProg ∧
    StepRespects stallProg (runStep stallProg) ∧ ¬ Terminates (runStep stallProg)

-- definitions and fixtures
WeakSelfArcCriterion P =
  ∀ G, InClosure P G → G.src = G.dst → G.comp G = G → ∃ i, G.lab i i ≠ Label.absent
runStep P s t = ∃ G ∈ P.calls, G.src = s.1 ∧ G.dst = t.1 ∧ Respects G s.2 t.2
gStall    : SCG 1 2 := arcsG f0 f0 [(0, 0, .nonstrict), (0, 1, .strict)]   -- f(x, x - 1)
stallProg : Prog 1 2 := ⟨[gStall]⟩
```

**Hypothesis ledger.** None: this is a closed statement about concrete programs (all of its parts are proved for the named instances).

**Depth:** shallow. The closure is the single idempotent graph; the run (1, 0), (1, 0), ... respects it; a thread must stay on x.

**Non-vacuity witness:** Concrete program stallProg. (Lean: `stall_weakSelfArcCriterion_counterexample`)

**Prior art:** [P1] (records under Evidence).

**Design question:** What exactly does a passed size-change (closure-criterion) check license about a recursive definition, and what does it not license?

**Non-claims:** see Boundaries, `nonstrict-self-arcs-insufficient`.

```text
Basis: execution (Lean kernel check)
```

#### `generators-insufficient`

**Claim.** For the program with calls f(x - 1, ?) (for x > 0) and f(?, y - 1) (for y > 0), every call-site graph has a strict self-arc and passes the idempotent test, but the composite of the two calls is the empty idempotent graph: the closure criterion fails, the program is not size-change terminating, it has an infinite consistent Nat run, and its most permissive model does not terminate.

**Tier:** T0. Instance of Theorem 4 of Lee, Jones and Ben-Amram, which tests the composition closure: the generator-only test is that criterion with the closure step removed, and altProg separates the two (its closure contains the empty idempotent loop). Same status as nonstrict-self-arcs-insufficient. Mechanized counterexamples to other incomplete descent criteria appear in Wright, Cohen, Rowe and Popescu (ITP 2026).

**Kind:** counterexample. **Lean:** `Toy.SCT.alt_generatorCriterion_counterexample`

```lean
theorem Toy.SCT.alt_generatorCriterion_counterexample :
    (∀ G ∈ altProg.calls, G.HasStrictSelfArc) ∧ GeneratorCriterion altProg ∧
    ¬ ClosureCriterion altProg ∧ ¬ SizeChangeTerminating altProg ∧ ConsistentRunIn Nat altProg ∧
    StepRespects altProg (runStep altProg) ∧ ¬ Terminates (runStep altProg)

-- definitions and fixtures
GeneratorCriterion P = ∀ G ∈ P.calls, G.src = G.dst → G.comp G = G → G.HasStrictSelfArc
gX : SCG 1 2 := arcsG f0 f0 [(0, 0, .strict)]      -- f(x - 1, ?)
gY : SCG 1 2 := arcsG f0 f0 [(1, 1, .strict)]      -- f(?, y - 1)
altProg : Prog 1 2 := ⟨[gX, gY]⟩
```

**Hypothesis ledger.** None: this is a closed statement about concrete programs (all of its parts are proved for the named instances).

**Depth:** shallow. Direct computation of one composite; the run alternates (1, 0) and (0, 1).

**Non-vacuity witness:** Concrete program altProg. (Lean: `alt_generatorCriterion_counterexample`)

**Prior art:** [P1], [P3], [P7] (records under Evidence).

**Design question:** Can the closure criterion be decided by a simple fixpoint computation whose acceptance is trustworthy, and what does rejection mean?

**Non-claims:** see Boundaries, `generators-insufficient`.

```text
Basis: execution (Lean kernel check)
```

#### `composition-tracks-strictness`

**Claim.** Composition must sequence labels exactly as <= ; < = <, < ; <= = < and <= ; <= = <=: if <= ; <= is taken to be <, the criterion accepts f(x) = f(x), which fails the standard criterion and has an infinite consistent run; if either mixed case is forgotten (<= ; < = <= or < ; <= = <=), the criterion rejects the mutually recursive mutProg (f0(x) = f1(x - 1) for x > 0, f1(y) = f0(y)), which satisfies the standard criterion, is size-change terminating and has no infinite consistent Nat run.

**Tier:** T1. Folklore about the composition of Lee, Jones and Ben-Amram (Definition 14); stated precisely here.

**Kind:** counterexample. **Lean:** `Toy.SCT.overStrict_composition_counterexample`, `Toy.SCT.forget_composition_rejects_mutProg`

```lean
theorem Toy.SCT.overStrict_composition_counterexample :
    CriterionWith Label.seqOverStrict idLoop ∧ ¬ ClosureCriterion idLoop ∧
    ¬ SizeChangeTerminating idLoop ∧
    ConsistentRunIn Nat idLoop ∧ StepRespects idLoop (runStep idLoop) ∧
    ¬ Terminates (runStep idLoop)
theorem Toy.SCT.forget_composition_rejects_mutProg :
    ¬ CriterionWith Label.seqForgetLeft mutProg ∧ ¬ CriterionWith Label.seqForgetRight mutProg ∧
    ClosureCriterion mutProg ∧ SizeChangeTerminating mutProg ∧ ¬ ConsistentRunIn Nat mutProg

-- definitions and fixtures
CriterionWith sq P = ∀ G, InClosureWith sq P G → G.src = G.dst → G.compWith sq G = G →
                       G.HasStrictSelfArc        -- ClosureCriterion P = CriterionWith Label.seq P
Label.seq:            ≤;≤ = ≤   ≤;< = <   <;≤ = <   <;< = <   (absent if either arc is absent)
Label.seqOverStrict:  any two present arcs give <
Label.seqForgetLeft:  as Label.seq except ≤;< = ≤
Label.seqForgetRight: as Label.seq except <;≤ = ≤
gId    : SCG 1 1 := arcsG f0 f0 [(0, 0, .nonstrict)];  idLoop : Prog 1 1 := ⟨[gId]⟩   -- f(x) = f(x)
gMut01 : SCG 2 1 := arcsG 0 1 [(0, 0, .strict)]       -- f0(x) calls f1(x - 1)
gMut10 : SCG 2 1 := arcsG 1 0 [(0, 0, .nonstrict)]    -- f1(y) calls f0(y)
mutProg : Prog 2 1 := ⟨[gMut01, gMut10]⟩
```

**Hypothesis ledger.** None: this is a closed statement about concrete programs (all of its parts are proved for the named instances).

**Depth:** shallow. Small closures computed by decision procedures in the kernel; size-change termination and absence of runs for mutProg come from closure-iff-sct and closure-criterion-sound.

**Non-vacuity witness:** Concrete programs idLoop and mutProg with the alternative sequencings Label.seqOverStrict, Label.seqForgetLeft and Label.seqForgetRight; both lossy sequencings still accept decLoop and swapDec (criterionWith_forgetLeft_pos, criterionWith_forgetRight_pos), so they are not degenerate. (Lean: `overStrict_composition_counterexample`, `forget_composition_rejects_mutProg`)

**Prior art:** [P1] (records under Evidence).

**Design question:** Can the closure criterion be decided by a simple fixpoint computation whose acceptance is trustworthy, and what does rejection mean?

**Non-claims:** see Boundaries, `composition-tracks-strictness`.

```text
Basis: execution (Lean kernel check)
```

#### `sct-incomplete-for-termination`

**Claim.** f(x) = if x < 100 then f(x + 1) else 0 terminates, yet every abstraction of it with one function and one parameter slot holding the raw argument x - every P : Prog 1 1 whose graphs describe all of its calls - fails the closure criterion.

**Tier:** T0. Known: Steila (TYPES 2014, Example 37) gives the counting-up program f(x, y) := if x > y then x else f(x + 1, y), which terminates but is not size-change terminating; Heizmann, Jones and Podelski (SAS 2010) show size-change termination is strictly stronger than termination. Restated here for a one-parameter counting-up loop, over all graph sets that describe its calls.

**Kind:** counterexample. **Lean:** `Toy.SCT.countUp_terminates_and_no_sound_prog_passes`

```lean
theorem Toy.SCT.countUp_terminates_and_no_sound_prog_passes :
    Terminates countUpStep ∧
    ∀ P : Prog 1 1, StepRespects P countUpStep → ¬ ClosureCriterion P

-- the model of f(x) = if x < 100 then f(x + 1) else 0
countUpStep s t = (t.1 = s.1 ∧ s.2 0 < 100 ∧ t.2 0 = s.2 0 + 1)
```

**Hypothesis ledger.** None: this is a closed statement about concrete programs (all of its parts are proved for the named instances).

**Depth:** shallow. The call 0 -> 1 rules out both labels on the only arc of the graph that justifies it, so P contains the empty graph, which is idempotent without a self-arc.

**Non-vacuity witness:** Concrete model countUpStep. (Lean: `countUp_terminates_and_no_sound_prog_passes`)

**Positive control:** Two nearby settings in which the closure criterion does certify termination. (1) On the raw argument, the counting-down loop f(x) = if x = 0 then 0 else f(x - 1) (model decStep s t = (t.1 = s.1 ∧ 0 < s.2 0 ∧ t.2 0 = s.2 0 - 1)) is certified: the one-function, one-slot program decLoop with the single graph x' < x describes all of its calls (StepRespects decLoop decStep), decLoop passes the closure criterion, and decStep terminates. (2) The counting-up loop itself is certified once the slot holds the size norm 100 - x instead of the raw argument x: every call s -> t of countUpStep respects the graph x' < x of decLoop on the values 100 - x (that is, 100 - x' < 100 - x), and decLoop passes the closure criterion. (Lean: `sct_incomplete_positive_control`, `countUp_size_norm_positive_control`)

**Prior art:** [P12], [P1], [P13], [P14] (records under Evidence).

**Design question:** What exactly does a passed size-change (closure-criterion) check license about a recursive definition, and what does it not license?

**Non-claims:** see Boundaries, `sct-incomplete-for-termination`.

```text
Basis: execution (Lean kernel check)
```

```text
Basis: execution (Lean v4.34.1 compiler run) + derived (modeling bridge)
```

Lean's own inference accepts `def countUp (x : Nat) : Nat := if x < 100 then countUp (x + 1) else 0` with the inferred measure `termination_by 100 - x` (probe `support/lean_inference_probes/Accepted.lean`, run 2026-11-20); a size-change checker on the raw argument cannot certify it, by this theorem.

### Lexicographic projection measures

#### `lex-implies-closure-criterion`

**Claim.** If for some length L and some choice ord of an L-tuple of parameters per function, the tuple of argument values decreases lexicographically on every call-site graph for all caller and callee values consistent with that graph, then the program satisfies the closure criterion. (By checker-correct, checkSCT then accepts it.) The kernel-checked theorem covers only programs with finitely many functions and finitely many parameter slots (Fin nf, Fin k): its statement quantifies over P : Prog nf k.

**Tier:** T1. Stated informally by Lee, Jones and Ben-Amram ('naturally subsumes ... the lexical ordering') and by Ben-Amram (2002: size-change termination extends and subsumes lexicographic descent); here made precise for lexicographic tuples of parameter projections that decrease for all graph-consistent values.

**Kind:** theorem. **Lean:** `Toy.SCT.closureCriterion_of_lexProjDecreases`

```lean
theorem Toy.SCT.closureCriterion_of_lexProjDecreases {nf k L : Nat} (P : Prog nf k)
    (ord : Fin nf → Fin L → Fin k) (h : LexProjDecreases P ord) : ClosureCriterion P

-- unfolded
LexProjDecreases P ord =
  ∀ G ∈ P.calls, ∀ u v : Fin k → Nat, Respects G u v →
    LexLt (fun l => v (ord G.dst l)) (fun l => u (ord G.src l))
LexLt a b = ∃ l : Fin L, (∀ i : Fin L, i.val < l.val → a i = b i) ∧ a l < b l
```

**Hypothesis ledger.**

| Hypothesis | Why it is needed | Tightness |
| :--- | :--- | :--- |
| h : LexProjDecreases P ord | The measure must decrease on every call, justified by the graph alone. | tight: counterexample `idLoop_no_lexProjDecreases_not_criterion` |

**Depth:** shallow. Via closure-criterion-exact: a failing criterion yields an infinite consistent Nat run, along which the measure would decrease lexicographically forever, contradicting well-foundedness of the lexicographic order on Nat^L (lexLt_no_infinite_descent). (Depth labels in this package are marginal: they measure the argument needed given the earlier results of the package.)

**Non-vacuity witness:** The Ackermann call structure (calls f(x - 1, ?) and f(x, y - 1)) with measure (x, y). (Lean: `lex_implies_closure_criterion_nonvacuous`)

**Prior art:** [P15], [P16], [P14] (records under Evidence).

**Design question:** How does a size-change checker compare in power with checkers that search for lexicographic measures over parameters (as Lean's termination inference does)?

**Non-claims:** see Boundaries, `lex-implies-closure-criterion`.

```text
Basis: execution (Lean kernel check)
```

```text
Basis: source + execution (Lean v4.34.1) + derived (modeling bridge)
```

Lean's termination inference searches lexicographic combinations of measures (`GuessLex.lean` module documentation); this theorem covers only lexicographic tuples of single parameter projections justified by the graphs alone, so it does not show that `checkSCT` accepts every definition Lean's inference accepts (Lean also uses measures `e2 - e1` from guards and orders on functions).

#### `sct-not-lex`

**Claim.** The permuting call f(x, y) = f(y, x - 1) (for x > 0) satisfies the closure criterion, is accepted by checkSCT, and its model (f(x, y) = if x = 0 then 0 else f(y, x - 1)) respects its graph and terminates; yet no lexicographic tuple of single-parameter projections, of any length, decreases on its call, neither for all graph-consistent values nor on the model's own calls.

**Tier:** T1. Lee, Jones and Ben-Amram note that their permuted-parameter examples 'seem to possess no natural lexical descent'; here a simpler permuting call is shown to have no decreasing lexicographic projection measure at all, both relative to its graph and relative to its model.

**Kind:** counterexample. **Lean:** `Toy.SCT.swapDec_closureCriterion_and_no_lexProjDecreases`

```lean
theorem Toy.SCT.swapDec_closureCriterion_and_no_lexProjDecreases :
    ClosureCriterion swapDec ∧ checkSCT swapDec = true ∧
    StepRespects swapDec swapStep ∧ Terminates swapStep ∧
    (∀ (L : Nat) (ord : Fin 1 → Fin L → Fin 2), ¬ LexProjDecreases swapDec ord) ∧
    (∀ (L : Nat) (ord : Fin 1 → Fin L → Fin 2),
      ¬ ∀ s t, swapStep s t → LexLt (fun l => t.2 (ord t.1 l)) (fun l => s.2 (ord s.1 l)))

-- fixtures
gSwap   : SCG 1 2 := arcsG f0 f0 [(1, 0, .nonstrict), (0, 1, .strict)]   -- x' ≤ y, y' < x
swapDec : Prog 1 2 := ⟨[gSwap]⟩
swapStep s t = (t.1 = s.1 ∧ 0 < s.2 0 ∧ t.2 0 = s.2 1 ∧ t.2 1 = s.2 0 - 1)
```

**Hypothesis ledger.** None: this is a closed statement about concrete programs (all of its parts are proved for the named instances).

**Depth:** shallow. The first component of any such tuple is x or y, and an explicit call makes it increase: (1, 2) -> (2, 0) increases x and (2, 0) -> (0, 1) increases y.

**Non-vacuity witness:** Concrete program swapDec and model swapStep. (Lean: `swapDec_closureCriterion_and_no_lexProjDecreases`)

**Positive control:** The Ackermann call structure ackProg (calls f(x - 1, ?) and f(x, y - 1); fixtures quoted under no-run-length-bound) does have a decreasing lexicographic projection measure, ackOrd = (x, y) (LexProjDecreases ackProg ackOrd), and satisfies the closure criterion, so a program accepted by the criterion can have such a measure; swapDec has none. (Lean: `sct_not_lex_positive_control`)

**Prior art:** [P15], [P10], [P14], [P17], [P6] (records under Evidence).

**Design question:** How does a size-change checker compare in power with checkers that search for lexicographic measures over parameters (as Lean's termination inference does)?

**Non-claims:** see Boundaries, `sct-not-lex`.

```text
Basis: execution (Lean kernel check)
```

```text
Basis: execution (Lean v4.34.1 compiler run) + derived (modeling bridge)
```

Lean's inference rejects `def swapF (x y : Nat) : Nat := if x = 0 then 0 else swapF y (x - 1)` with "Could not find a decreasing measure" and accepts it with `termination_by x + y` (probes `support/lean_inference_probes/SwapRejected.lean` and `Accepted.lean`, run 2026-11-20). This is an observation on one example, not a theorem about Lean.

### Auxiliary lemma

#### `ramsey` (auxiliary lemma)

**Claim.** Auxiliary lemma (not a headline result of this package): For any colouring col of the pairs m < n of natural numbers whose colours all lie in a finite list S, there is a strictly increasing h : Nat -> Nat and a colour a with col (h m) (h n) = a for all m < n.

**Tier:** T0. Ramsey's theorem for pairs (infinite version, finitely many colours) restated over Nat; included as an auxiliary statement because the soundness direction of the closure criterion is classically proved from it.

**Kind:** theorem. **Lean:** `Toy.SCT.infinite_ramsey_pairs_of_finite_colors`

```lean
theorem Toy.SCT.infinite_ramsey_pairs_of_finite_colors {α : Type} (S : List α) (col : Nat → Nat → α)
    (hS : ∀ m n, m < n → col m n ∈ S) :
    ∃ h : Nat → Nat, (∀ m n, m < n → h m < h n) ∧
      ∃ a : α, ∀ m n, m < n → col (h m) (h n) = a
```

**Hypothesis ledger.**

| Hypothesis | Why it is needed | Tightness |
| :--- | :--- | :--- |
| hS : ∀ m n, m < n → col m n ∈ S (finitely many colours) | With infinitely many colours there need not be any homogeneous infinite set. | tight: counterexample `ramsey_infinite_colors_counterexample` |

**Depth:** substantive. Proved by iterated infinite pigeonhole (Toy/SCT/Ramsey.lean): repeatedly pick a candidate position and shrink the infinite candidate set to the positions whose pair with it has one colour, then apply pigeonhole once more to the chosen colours. Needs explicit construction of infinite sequences by choice; no library support.

**Non-vacuity witness:** The parity colouring (m + n) % 2 takes values in [0, 1]; h n = 2 n is homogeneous of colour 0. (Lean: `infinite_ramsey_nonvacuous`)

**Prior art:** [P18], [P1], [P4], [P19], [P20] (records under Evidence).

**Design question:** Reference point: which combinatorial principle does a mechanized proof of size-change soundness have to supply when no library provides it?

**Non-claims:** see Boundaries, `ramsey`.

```text
Basis: execution (Lean kernel check)
```

## Boundaries

### Non-claims (per result)

Each list states what the result does **not** show. Read it together with the result's hypotheses.

#### `closure-iff-sct`

- Both sides are properties of the size-change graphs only. Neither says anything about a real program unless its calls respect the graphs (card graphs-must-be-sound).
- Size-change termination here quantifies over all infinite paths through the call sites, regardless of guards or reachability; it is not a statement about the paths a real program can actually take.
- No complexity or efficiency claim: the closure can be exponentially large, and the problem is PSPACE-hard (Lee, Jones and Ben-Amram, Theorem 5; not formalized here).
- Only idempotent loop graphs (G.src = G.dst and G ; G = G) must have a strict self-arc; non-idempotent loop graphs in the closure of a size-change-terminating program may have no self-arc at all (for swapDec: its only call-site graph gSwap = arcsG f0 f0 [(1, 0, .nonstrict), (0, 1, .strict)], that is x' <= y and y' < x, and gSwap3 = gSwap ; gSwap ; gSwap = arcsG f0 f0 [(0, 1, .strict), (1, 0, .strict)], with strict cross-arcs x -> y' and y -> x' and no self-arc, which lies in the closure by comp_pos and inClosure_pos; idempotence_needed_for_converse).
- Unrooted model: every function is a possible entry point (as in Ben-Amram, LMCS 2010). Lee, Jones and Ben-Amram (POPL 2001, Definitions 10 and 16) restrict call sequences and the closure to calls reachable from a designated initial function, so a recursive function unreachable from it is ignored there but tested (and possibly rejected) here.
- Every function has the same number k of parameter slots; functions with fewer parameters are modelled by slots without arcs. Such slots do not affect the closure, the criterion, size-change termination, consistent runs or checkSCT, but they do affect lexicographic projection measures (card lex-implies-closure-criterion).
- Finiteness is essential and is not a removable side condition: finitely many functions are needed for the forward direction, finitely many parameter slots for both directions (counterexamples in the generalized model SCGInf, listed in the hypothesis ledger). Nothing is claimed for systems with infinitely many functions or parameters.

#### `sct-sound-nat`

- Only runs that respect the graphs at every step are excluded; a real program's calls must be shown to respect them separately.
- Over a non-well-founded value domain the conclusion fails: over Int, f(x) = f(x - 1) has the consistent run 0, -1, -2, ... (decLoop_closureCriterion_consistent_int_run).
- Generalizing from Nat to another value type would need not only well-foundedness of < but also the compatibility laws a < b <= c -> a < c and a <= b < c -> a < c (Ben-Amram, LMCS 2010, Definition 3.5); RespectsIn assumes no relation between < and <= on a general type, and nothing is claimed beyond Nat.
- No bound on run length is implied (card no-run-length-bound).

#### `closure-criterion-sound`

- It is a statement about the abstraction only. 'Passed' licenses termination of a real program only together with a proof that every real call respects one of the graphs (card closure-criterion-sound-model and graphs-must-be-sound).
- Over a non-well-founded value domain the conclusion fails (decLoop_closureCriterion_consistent_int_run).
- No bound on the number of calls (card no-run-length-bound).
- First-order calls only: the model has a fixed finite set of functions and explicit call sites; higher-order calls (calls through function-valued arguments) are outside the model, and nothing here covers them.
- It does not show that a program failing the criterion diverges (cards closure-criterion-exact and sct-incomplete-for-termination).
- Weakening any component of the criterion (generators only, nonstrict self-arcs, composition that over-claims strictness) breaks it (cards generators-insufficient, nonstrict-self-arcs-insufficient, composition-tracks-strictness).
- Unrooted model: every function is tested as a possible entry point (card closure-iff-sct); Lee, Jones and Ben-Amram (POPL 2001) consider only calls reachable from an initial function.
- Graphs abstract calls only under the program's guards: with truncated Nat subtraction an unguarded call f(x - 1) at x = 0 passes 0 and violates x' < x (card graphs-must-be-sound).

#### `closure-criterion-sound-model`

- StepRespects is an obligation about the real program that this theorem assumes and does not check; a checker that accepts unsound graphs proves nothing (card graphs-must-be-sound).
- Termination here means no infinite call sequence of the given relation; it says nothing about non-call sources of divergence (loops inside a function body, partial primitives) unless they are modelled as calls.
- Values are natural numbers, and there are finitely many functions and finitely many parameter slots (all three are built into State nf k and each is tight). A real size measure must map into Nat (another well-founded order is not covered here), and nothing is claimed for systems with infinitely many functions or parameters.
- No complexity bound (card no-run-length-bound).
- Totalized operations need their guards: over Nat, truncated subtraction gives 0 - 1 = 0, so an unguarded call f(x - 1) does not respect x' < x at x = 0 and StepRespects fails (misfit_graphs_counterexample); the same holds for total list operations such as tail [] = [].
- Connecting a functional program with nested calls (such as A(m - 1, A(m, n - 1))) to a call relation on evaluated argument states needs a separate call-by-value adequacy argument (Lee, Jones and Ben-Amram, Lemmas 2 and 3); under lazy or non-strict evaluation an infinite call chain need not mean divergence. Neither is modelled.

#### `graphs-must-be-sound`

- Does not show how to establish that graphs are sound for a real program; that is a separate size analysis outside this package.
- Totalized or saturating operations break graph soundness exactly at their base cases (0 - 1 = 0 over Nat, tail [] = [] for lists); such calls respect a strict arc only on paths guarded by x > 0 (or a non-empty test).

#### `no-run-length-bound`

- The unboundedness comes from one state having infinitely many possible successors in the abstraction (an unconstrained callee argument). A deterministic or finitely branching call relation that terminates has a finite maximum run length from each start state (a classical consequence of Konig's lemma, not formalized here).
- The same graphs ackProg also describe the deterministic, linear-time program f(x, y) = if x > 0 then f(x - 1, y + 1) else if y > 0 then f(x, y - 1) else 0 (stepRespects_ackLinStep); the non-primitive-recursive growth of the real Ackermann function comes from its nested call A(m - 1, A(m, n - 1)) supplying the second argument, which this abstraction does not see. No growth rate of any real program is claimed.
- A lexicographic measure does not bound run length either; the issue is not specific to size-change termination.

#### `closure-criterion-exact`

- The run exists in the abstraction (it respects the graphs). It need not be a run of any real program: rejection by the checker does not mean the real program diverges (card sct-incomplete-for-termination).
- Together with closure-criterion-sound it characterizes the criterion as exactly 'no consistent infinite Nat run' for this abstraction; it does not characterize termination of real programs.
- No value bound and no computability claim is stated in Lean. By inspection of the proof the construction is explicit, with values at most (m + 1) * (k + 2) for a factor path of length m, but this bound is not formalized, and no claim is made about computing the run from P.

#### `checker-correct`

- Not an efficient algorithm: the closure may have exponentially many graphs; the decision problem is PSPACE-hard (Lee, Jones and Ben-Amram, Theorem 5), which is not formalized here.
- Specification-level cost: the fuel nf * nf * 3^(k*k) + 1 already exceeds 4 * 10^7 for one function with k = 4, and each iteration step scans all pairs of the current list with list-membership tests (cubic in the list length); direct execution or kernel evaluation is impractical except for tiny closures.
- The checker computes the full closure. Optimizations such as subsumption change what must be tested (Ben-Amram, LMCS 2010, Section 4.3) and are not covered.
- Correctness is relative to the closure criterion, a property of the graphs; it carries no information about whether the graphs are sound for a real program.
- The fuel is fixed by the definition; with too little fuel the iteration gives up and the checker rejects (closureIter_neg).
- Unrooted: the closure contains the composites of all call paths, from every function (card closure-iff-sct).
- Composition is total (it does not check G.dst = H.src, unlike the partial composition of Lee, Jones and Ben-Amram, Definition 14); the closure only composes composable pairs, and the loop guard G.src = G.dst in the test is what excludes non-loop graphs that are idempotent as label matrices.
- The finite function set and parameter slots are preconditions of the definition (the fuel counts the graphs of the finite type SCG nf k), not hypotheses that could be dropped; no checker for infinite systems is considered.

#### `nonstrict-self-arcs-insufficient`

- Shows only that the criterion cannot be weakened to nonstrict self-arcs; it says nothing about other weakenings.
- Strict arcs between different parameters (here x -> y') do not substitute for a strict self-arc on an idempotent graph.

#### `generators-insufficient`

- Shows that checking generators is unsound; it does not say how much of the closure an optimized checker may omit (for subsumption see Ben-Amram, LMCS 2010, Section 4.3).

#### `composition-tracks-strictness`

- Over-claiming breaks soundness; forgetting a mixed case breaks completeness. Whether the forgetful criteria are sound is neither claimed nor refuted.
- Only these three alternative sequencings are examined.

#### `sct-incomplete-for-termination`

- Rejection by the checker is not evidence of divergence.
- The impossibility fixes nf = 1, k = 1 and identifies the single slot with the raw argument x. Within plain size-change graphs (no difference constraints) the loop is certified as soon as the abstraction changes: measured by the size norm 100 - x every call respects x' < x (countUp_size_norm_positive_control); a second slot tracking 100 - x, or splitting the 101 values into acyclic control points, also works (not formalized).
- Richer abstractions (difference constraints, guards) can also certify this loop, and Lean's own inference accepts it via a measure 100 - x derived from the guard (observation recorded in prior art).

#### `lex-implies-closure-criterion`

- The measure must decrease for every pair of argument vectors consistent with the graph, not merely on the calls a real program makes. A measure that decreases on real calls but relies on information absent from the graphs (arithmetic facts like x + 1 > x, or the branch taken inside one call site) does not make the criterion pass.
- Single-graph limit: a call site is described by one conjunctive graph. For f(x, y) = f(if y = 0 then x - 1 else x, if y = 0 then 5 else y - 1) every real call decreases (x, y) lexicographically, but the only sound single graph is x' <= x, which fails the criterion unless the call site is split into its two branches (as in ackProg).
- Decrease is required on every single call site, not around cycles: mutProg (f0(x) = f1(x - 1) for x > 0, f1(y) = f0(y)) passes the criterion and checkSCT but has no such measure of any length (mutProg_closureCriterion_no_lexProjDecreases); Lean's inference (with an order on functions) and Ben-Amram's cycle-based lexicographic descent (2002) handle such programs.
- Padding slots: a function with zero real parameters still needs projections onto arc-free slots, which are unconstrained on every call into it; the non-recursive acycProg : Prog 2 1 := ⟨[gAcyc]⟩ with gAcyc : SCG 2 1 := arcsG 0 1 [] (two functions with one slot each; f0 calls f1 once with no size information, and f1 makes no calls) has no such measure (acycProg_closureCriterion_no_lexProjDecreases).
- Only lexicographic tuples of single parameter projections; measures such as sums, maxima or multisets of parameters are not covered.
- All functions use tuples of the same length; an order on the functions themselves (used by Lean's inference for mutual recursion) is not modelled.
- No comparison with Lean's termination inference is proved: checkSCT and Lean's inference are incomparable on examples (swapDec is accepted only by checkSCT; guarded counting-up loops, function-ordered mutual recursion and unsplit conditional calls only by Lean; observations recorded in prior art).
- The converse is false (card sct-not-lex).

#### `sct-not-lex`

- The separation is only against lexicographic tuples of single parameters. It does not mean arithmetic is needed for a ranking function: the order-based measure max(2x, 2y + 1) (the lexicographic maximum of <x, 0> and <y, 1>) decreases on every graph-consistent step (swapDec_order_ranking), and every terminating size-change instance has a global ranking function built from minima and maxima of lexicographically ordered tuples of variables and constants (Lee, TOPLAS 2009, as summarized by Ben-Amram and Lee, LMCS 2009); x + y also works.
- The extra power is in which programs are certified, not in which functions can be computed: size-change-terminating programs compute exactly the multiply-recursive functions, the same class as lexicographic descent (Ben-Amram 2002, not formalized here).
- checkSCT is not claimed to be stronger than Lean's termination inference overall: they are incomparable on examples (card lex-implies-closure-criterion and sct-incomplete-for-termination); the separation from Lean is an observation on one example (recorded in prior art), not a theorem about Lean.
- One program; no claim about how often such programs occur.

#### `ramsey`

- Only the infinite version for pairs and finitely many colours; no finite Ramsey numbers, no hypergraph version, no bounds.
- The homogeneous colour a is not computed; the statement is purely existential.
- It is not claimed that Ramsey's theorem is necessary for size-change soundness; intuitionistic alternatives exist in the literature (Vytiniotis, Coquand and Wahlstedt 2012; Steila 2015).
- Proof-theoretic strength is not addressed: the size-change characterization does not need the full strength of Ramsey's theorem for pairs (over RCA_0 the SCT criterion is equivalent to Sigma^0_2 induction and needs only a triangle corollary of Ramsey's theorem; Frittaion, Steila and Yokoyama, TAMC 2017). The package proves the full infinite version for pairs because it is simple to state and to apply.

### Escape hatches (which assumptions, if changed, defeat a negative result)

- `sct-incomplete-for-termination` fixes one function, one parameter slot, and identifies the slot with the raw argument `x`. Changing the abstraction defeats it: measured by the size norm `100 - x`, every call respects `x' < x` and `decLoop` passes (`countUp_size_norm_positive_control`); a second slot tracking `100 - x`, or splitting the 101 values into acyclic control points, also works (not formalized). Richer abstractions (difference constraints, guards) and Lean's own inference (measure `100 - x`) also certify the loop.
- `sct-not-lex` is only against lexicographic tuples of single parameter projections. Other measures defeat it: `max(2x, 2y + 1)` decreases on every graph-consistent step (`swapDec_order_ranking`), and so does `x + y`.
- `no-run-length-bound` relies on an unconstrained callee argument, i.e. infinitely many possible successors of one state. For a finitely branching terminating call relation, a finite maximum run length from each start state follows classically by König's lemma (not formalized). `decLoop` has runs of length at most its argument (`no_run_length_bound_positive_control`).
- `nonstrict-self-arcs-insufficient`, `generators-insufficient` and `composition-tracks-strictness` refute specific weakenings of the test; each counterexample is a concrete program, and other weakenings are not examined.
- `closure-criterion-exact` constructs a run of the abstraction only; a real program rejected by the checker may still terminate (`sct-incomplete-for-termination`).

### Hypotheses with `unknown` tightness and open questions

- No hypothesis in this package has tightness `unknown`. One is labelled `harmless`: finiteness of the function set in `closure-criterion-exact` (the construction uses finiteness of the parameter slots only).
- Not examined: whether the criteria with the lossy sequencings `Label.seqForgetLeft` or `Label.seqForgetRight` are sound (they are shown incomplete only).
- Not examined: complexity of the decision problem (PSPACE-hardness, Lee, Jones and Ben-Amram, Theorem 5, is cited, not formalized); value bounds of the run built by `closure-criterion-exact` (stated only by inspection of the proof).

### Refuted or withdrawn candidate statements

None of the 15 results was found false, and none was withdrawn: all are proved as stated. The following nearby statements are false, and the package records why:

- *"A program satisfying the closure criterion has no infinite consistent run, for any value type."* False over `Int`: `f(x) = f(x - 1)` satisfies the criterion and has the consistent run `0, -1, -2, …` (`decLoop_closureCriterion_consistent_int_run`); its model over integer states does not terminate (`decLoop_int_model_counterexample`).
- *"The criterion is sound and complete with infinitely many functions or parameters."* False: `infinite_functions_counterexample`, `infinite_params_soundness_counterexample`, `infinite_params_converse_exactness_counterexample` (generalized model `SCGInf`), with model-level forms `infinite_functions_model_counterexample` and `infinite_params_model_counterexample`.
- *"A lossy composition that forgets strictness whenever two present arcs are sequenced (every present pair gives `≤`) is a useful separating variant."* It is degenerate: it can never produce a strict arc, so its criterion rejects every program with an idempotent loop. The package instead uses `Label.seqForgetLeft` and `Label.seqForgetRight`, which differ from `Label.seq` in exactly one mixed case each and still accept `decLoop` and `swapDec` (`criterionWith_forgetLeft_pos`, `criterionWith_forgetRight_pos`).
- *"The lexicographic maximum of `(x, 1)` and `(y, 0)` ranks `f(x, y) = f(y, x - 1)`."* False: on the graph-consistent step `(1, 2) → (2, 0)` it increases from `(2, 0)` to `(2, 1)`. The order-based measure `max(2x, 2y + 1)` (the lexicographic maximum of `(x, 0)` and `(y, 1)`, encoded in `Nat`) does decrease (`swapDec_order_ranking`).
- *"Size-change termination of the abstraction bounds the number of calls from a start state."* False in the abstraction (`ackProg_unbounded_finite_runs`).

## Evidence

### Kernel-check record

Every declaration of the library (`Toy.*`, 511 non-internal declarations) was checked by the Lean `v4.34.1` kernel; `audit/axioms.json` records, per declaration, the axioms reported by `Lean.collectAxioms` (the content of `#print axioms`), and every entry is a subset of `propext`, `Classical.choice`, `Quot.sound`. No source file contains `sorry`, `admit`, `native_decide`, `axiom`, `opaque`, `implemented_by`, `extern` or `unsafe`. The build also runs `Toy/SCT/Audit.lean`, which fails the build if any declaration depends on `sorryAx` or on a non-standard axiom.

The table lists every declaration named in a result card's structured Lean fields (`lean`, `nonvacuity_witness_lean`, `positive_control_lean` and hypothesis `counterexample` in `results.json`), 42 declarations. Supporting lemmas cited only in prose (for example `infinite_functions_model_counterexample`, `infinite_params_model_counterexample`, `inClosure_iff_inClosureInf`, `swapDec_order_ranking`, `lexLt_no_infinite_descent`) carry no recorded statement hash; like every library declaration they are kernel-checked and their axioms are recorded in `audit/axioms.json`. The statement hash is the SHA-256 of `repr` of the declaration's type; the closure hash is the SHA-256 of the sorted lines `name : repr type := repr value` (value omitted for theorems) of every library constant reachable from the type through types and definition bodies; the closure size counts those constants. `audit/statements.json` holds the same values; `support/revalidate.py` recomputes them. A closure size of 0 (closure hash `e3b0c442…`, the SHA-256 of the empty string) means the statement mentions no library definition, only core Lean.

| Declaration | Role (card) | Axioms (`#print axioms`) | Statement SHA-256 | Closure SHA-256 (size) |
| :--- | :--- | :--- | :--- | :--- |
| `ackProg_unbounded_finite_runs` | no-run-length-bound: non-vacuity; no-run-length-bound: result | `Quot.sound`, `propext` | `3cfd850dca2b24f39873182876b4291eef092a1552818dac30dc54cabf13f64a` | `fcedf9fdf36ccbc2d2b46c6c85f7de00ded0b45d9a5d83afbadc3572208a8ec9` (43) |
| `alt_generatorCriterion_counterexample` | closure-criterion-sound: counterexample; closure-iff-sct: counterexample; generators-insufficient: non-vacuity; generators-insufficient: result | `Classical.choice`, `Quot.sound`, `propext` | `2f4061ca5c0c4c57bc3a0be758764f6cd47f80961632dff942a82dca3bc2d69a` | `00377630be1846cd229f93907306c56fcc53795201fa1d9ecd44382802bfeabc` (48) |
| `checkSCT_eq_true_of_closureCriterion` | checker-correct: result | `Classical.choice`, `Quot.sound`, `propext` | `7d30caf6d678651e887e33d7944d8fd759eb1a1d3be2df0447b1f875521b41e5` | `88e78b04a8088f85a00cbcd56b0e93d6df2eac77a7c95d90e3485d44b8763777` (47) |
| `checker_correct_nonvacuous` | checker-correct: non-vacuity | `Quot.sound`, `propext` | `9f5113ea153fe397557ea64351ce0fd25146fed284cb3f11a32e700b7a5ce9e7` | `af2b126edd3fa823bf6a0fbab0d8fdbc99363f29925e14f86336d272906e7647` (54) |
| `checker_premise_contrast` | checker-correct: counterexample | `Quot.sound`, `propext` | `14de4a25bd4108df737b470ac6874630b8027a78ab2422385c6d477431e187c4` | `f61ef481557114804f9ff3eb04fd80bfd394f4f665f2bfb04d7906abb2bdc2f8` (54) |
| `closureCriterion_of_checkSCT_eq_true` | checker-correct: result | `Quot.sound`, `propext` | `d393e6f58ec3c6e8ace67d0b95c7f7a4893178db68df19c250e720b7cd65fb00` | `88e78b04a8088f85a00cbcd56b0e93d6df2eac77a7c95d90e3485d44b8763777` (47) |
| `closureCriterion_of_lexProjDecreases` | lex-implies-closure-criterion: result | `Classical.choice`, `Quot.sound`, `propext` | `64c0de969d09693df7d4f8e61e7ed918d9c8fb413797a891788b304306faf1b7` | `737133c508c71b22f2c13e8588290563fd9aaa72363ca01714f526b65ce5fdec` (32) |
| `closureCriterion_of_sizeChangeTerminating` | closure-iff-sct: result | `Classical.choice`, `Quot.sound`, `propext` | `94b5b6bf3c44aadb1a6cbaf345f5b814be7448295f2d5544d1b67534496185f6` | `6c7f389f7dc47016902b7a83c198f722243f9351f2a518dd514d3b7a725aa385` (31) |
| `closure_criterion_exact_nonvacuous` | closure-criterion-exact: non-vacuity | `Quot.sound`, `propext` | `925179f7b2751f550ffe32584cef17a1ec3d7ae61ac9ea8b9382af26e1000112` | `4906127accabfe25bdf6742edf5ca3dfb79d9197bab94545cbb0a54c3c5a9544` (38) |
| `closure_criterion_sound_model_nonvacuous` | closure-criterion-sound-model: non-vacuity | `Classical.choice`, `Quot.sound`, `propext` | `bb2a75f9f76bed8ebf21627e93b224ea1e09901cdaa16197e1aee351baa08fe1` | `b296aeb192c9008c29dd3ad90ee84c2d7244d2d8692828c6783c243aeeb536a8` (41) |
| `closure_criterion_sound_nonvacuous` | closure-criterion-sound: non-vacuity | `Quot.sound`, `propext` | `d1379fb9ec996c80f8ccbe894bf7bb2f1f1728fc81c79f336eff377ce10bfd81` | `b53f7049f80c4e89ad4e0180a21b9a3f8d562dc9a182b2e860435f027de6ddd5` (42) |
| `closure_iff_sct_nonvacuous` | closure-iff-sct: non-vacuity | `Quot.sound`, `propext` | `66fb73f505b31f6ae214a771f5ac4c169637dc5a1709249609cd5349cdfba728` | `48755c7ce10ca2a2f6993b572d85140b69d99eed6aaf7ca23b7be0c88610c824` (40) |
| `consistent_nat_run_of_not_closureCriterion` | closure-criterion-exact: result | `Classical.choice`, `Quot.sound`, `propext` | `e1fb0550c6873e0c1387937438d0c4e7ddb69d6895685f38e7c18d39ac780261` | `fd024ac634d5a94c59d45772accfbb1fd8ae56203185d2ebb995e2af9eb87f1a` (30) |
| `countUp_size_norm_positive_control` | sct-incomplete-for-termination: positive control | `Quot.sound`, `propext` | `9a567e7ecc73263838487a5d6606d0a946d70dab1a93264d274f3a21de8bbfa1` | `e1613770a5ccdf0157fe7fa2ad2887a69fa05e71b0427decfe3713f3e7588cd7` (39) |
| `countUp_terminates_and_no_sound_prog_passes` | sct-incomplete-for-termination: non-vacuity; sct-incomplete-for-termination: result | `Quot.sound`, `propext` | `ec28aa52f46fe92e032d45e3691c4229cf8d9536ec9775be46563391662e455b` | `2ad15bcdbada3c53871f0d75bfe357ec48ea1d4607acc9a49425ff2f34527e84` (35) |
| `decLoop_closureCriterion_consistent_int_run` | closure-criterion-sound: counterexample; sct-sound-nat: counterexample | `Quot.sound`, `propext` | `8cd9cfe0c5f2dfeba00d66a6d270364d30218d5adb8909f2768a9c85e0ccec70` | `4047b284676a77be76c1f07dcec5b3ad00c7941f03a9c51d1fa3589525570949` (40) |
| `decLoop_int_model_counterexample` | closure-criterion-sound-model: counterexample | `Quot.sound`, `propext` | `c2ce058b35f5466c8946ed0405dee97bc5df8d849b5da38ff1df7fa5159f28dd` | `0782146fd29a3638f7a0148ee2fe7c099b7064356c5adf3c72b48a01c1d18f8d` (37) |
| `forget_composition_rejects_mutProg` | closure-iff-sct: counterexample; composition-tracks-strictness: non-vacuity; composition-tracks-strictness: result | `Classical.choice`, `Quot.sound`, `propext` | `860b74e346d6563752603dd3d49c508fea8b0a89718ec6c7bea4a8d796f6a267` | `427f4cc08adab76de14db37f0873ad5a0a896ef5a0720aef09e26b496dd68cb7` (45) |
| `idLoop_decLoop_contrast` | closure-criterion-exact: counterexample; closure-iff-sct: counterexample; sct-sound-nat: counterexample | `Quot.sound`, `propext` | `39e62cd529768817c703d7bbf8a56db8d1f4f37b3cd66326b74c6022d4769cd1` | `7a8c57dfc4836af244a9116008742b32cd4517f8a486084daa8eab98c03b6caa` (42) |
| `idLoop_no_lexProjDecreases_not_criterion` | lex-implies-closure-criterion: counterexample | `Quot.sound`, `propext` | `0a6af91bd745beecfa96b1614c5db1c1d49d0f8f10aad658830c88b6e5086064` | `573cfb2ec1fbabc750b33c7e58b3a0773d241d7cfb7b19ed27e17460d8d13499` (39) |
| `idLoop_runStep_counterexample` | closure-criterion-sound-model: counterexample | `Classical.choice`, `Quot.sound`, `propext` | `e99dae3c533707161b15ca4f27204cce8c003452c82a74e4064fa19c1e58cef2` | `d87f129d3e1d9b737e4678a53913d59d499635b6c5ff6858dfb307b6febcdef8` (41) |
| `idempotence_needed_for_converse` | closure-iff-sct: counterexample | `Quot.sound`, `propext` | `e1912123907cfb1ed9c2b02d7e6cc034e8d08537ab21671d87c99eb3302f8773` | `c2a8dfff86bc5a1fe3a60c73054ef2f6279b7aeda77799913a8776fc36be2f48` (40) |
| `infinite_functions_counterexample` | closure-criterion-sound-model: counterexample; closure-criterion-sound: counterexample; closure-iff-sct: counterexample | `Classical.choice`, `Quot.sound`, `propext` | `5bc78498eeee799dceb46ce419334b86731e8fd27439c366e7a57541b53a2203` | `73e5b5abd029d7ff0678ea696690b27887d9b51c5e856e79d30f2bc119420188` (24) |
| `infinite_params_converse_exactness_counterexample` | closure-criterion-exact: counterexample; closure-iff-sct: counterexample | `Classical.choice`, `Quot.sound`, `propext` | `bab83613c2cb023feb8019b2e293bfb28cc0f2ddd1ec31fb95e42f2cabf1cf16` | `eea90fd2bafccd64a92365fc87ee17ca22a12825751d170a38e15ae9651d7748` (30) |
| `infinite_params_soundness_counterexample` | closure-criterion-sound-model: counterexample; closure-criterion-sound: counterexample; closure-iff-sct: counterexample | `Classical.choice`, `Quot.sound`, `propext` | `2ab220c0c2d2b9d52c9a59ef18d77734783a6afdf43404dd47b0e75270a642f0` | `8e3d0995a9fcda2e3b268141dd05e97d1b59db5dcf8a6401d822b3d5dc2fe685` (27) |
| `infinite_ramsey_nonvacuous` | ramsey: non-vacuity | `Quot.sound`, `propext` | `a0752b2986bcec33e949ac81351462510f9bfb4bf140cc6443c4e4c2bf505b42` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `infinite_ramsey_pairs_of_finite_colors` | ramsey: result | `Classical.choice`, `Quot.sound`, `propext` | `dc894a91b4499cb56cf95283aa7c08fbe90851b93ceee6a3710df58c9f4a878f` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `lex_implies_closure_criterion_nonvacuous` | lex-implies-closure-criterion: non-vacuity | `Quot.sound`, `propext` | `dcb7f1358c0a3017a79bf404e3922f0d4d8c6415f4b93624a84428c7861e671d` | `4b4b5971da2929975fa10f25b3c2d22c788dc5a96a87d3926e9b80c58d19a50d` (25) |
| `loop_guard_needed_for_converse` | closure-iff-sct: counterexample | `Quot.sound`, `propext` | `3376964b6ed995649c0ab01e17dc141f0b4dfd22ef2dc11fffc1cd8119446e4f` | `b5a59576e9093b7b297ec66c5f76d42d814d392e50ec466def6fd936170c9412` (40) |
| `misfit_graphs_counterexample` | closure-criterion-sound-model: counterexample; graphs-must-be-sound: non-vacuity; graphs-must-be-sound: result | `Quot.sound`, `propext` | `98ec791fe460078c3505449448743f786dfa2c76d82289f346af829b8b881661` | `b2fdeac6668611768a7169de5e6e54103a5afac637da1f181781f89f8d88beb2` (62) |
| `no_consistent_nat_run_of_closureCriterion` | closure-criterion-sound: result | `Classical.choice`, `Quot.sound`, `propext` | `cde9c40194e81807f6919c7c9f3f2cc50bc7a3d1d58c7eaad9f281bb215ee23c` | `fd024ac634d5a94c59d45772accfbb1fd8ae56203185d2ebb995e2af9eb87f1a` (30) |
| `no_consistent_nat_run_of_sizeChangeTerminating` | sct-sound-nat: result | `Quot.sound`, `propext` | `513bd2545d213aa4ad39205e92e76045366ce538d563d64b9f3cd3ef6591f814` | `c3af99a122a6f1cef3141ee5e71ec654fe42417de2536d2904400835a38bbc58` (17) |
| `no_run_length_bound_positive_control` | no-run-length-bound: positive control | `Quot.sound`, `propext` | `a344c7c026207b1430fbfd5441299e14de32393bcaadd12bb27027efb14e71b5` | `ce1130e52859f64696a9127837ec270876b7695d9bd59e6e868663ec999009b2` (22) |
| `overStrict_composition_counterexample` | closure-criterion-sound: counterexample; closure-iff-sct: counterexample; composition-tracks-strictness: non-vacuity; composition-tracks-strictness: result | `Classical.choice`, `Quot.sound`, `propext` | `6fd88fdfc56e099085e353bee390643bd0d38b27434db2010607611733841302` | `2a6ffca3edbccaffbc80dcf4c06516d107d350fb25963573dab060f1ef3832e2` (48) |
| `ramsey_infinite_colors_counterexample` | ramsey: counterexample | `Quot.sound`, `propext` | `ebb67e77f51aa37a9ea6096e86d9a3e7fd9f8e434501137d412c348654f086fc` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `sct_incomplete_positive_control` | sct-incomplete-for-termination: positive control | `Quot.sound`, `propext` | `96836c31d36a8a84a12f4ca66d6cecc270d77a10758d8790bae559cba817992a` | `4f0347c87632c912403c3af8a2d2c3a70bbc90df2358da46b097692b5e35199a` (41) |
| `sct_not_lex_positive_control` | sct-not-lex: positive control | `Quot.sound`, `propext` | `638a5e2beb3219b8624efa231081a319684084034da82c10941522c0364247fe` | `efb518be4076ce853a3ff6a59f18d59e738c4f02831cf75132a8dfc0bd5f010e` (41) |
| `sct_sound_nat_nonvacuous` | sct-sound-nat: non-vacuity | `Quot.sound`, `propext` | `bd73d27c4211ccc5d80781c2e5f2f7bf86e7279225f11e82104453a519174c31` | `95cc9ceef908eafd8553c5fa3dd2dbac5339a82f83dad53cf630f20ae6b662e1` (22) |
| `sizeChangeTerminating_of_closureCriterion` | closure-iff-sct: result | `Classical.choice`, `Quot.sound`, `propext` | `0b6dbc727426868173accc36615e203bb32dbf6d10a9fd4307546e5a63fc03f9` | `6c7f389f7dc47016902b7a83c198f722243f9351f2a518dd514d3b7a725aa385` (31) |
| `stall_weakSelfArcCriterion_counterexample` | closure-criterion-sound: counterexample; closure-iff-sct: counterexample; nonstrict-self-arcs-insufficient: non-vacuity; nonstrict-self-arcs-insufficient: result | `Classical.choice`, `Quot.sound`, `propext` | `fb82e17cf2b11f3eb017f61b5757df072b6d0cb651c7a19d186e36ce2d4c09bf` | `2daeaaf5aeecfcd366ca20223b67fc1359f9afe52f68cfb2eb8c9d6105a21151` (49) |
| `swapDec_closureCriterion_and_no_lexProjDecreases` | sct-not-lex: non-vacuity; sct-not-lex: result | `Classical.choice`, `Quot.sound`, `propext` | `40d2c5bc7c5848de63d004f2e7ace4b55d840cf3bbb8f5721c407135b0b8938a` | `3e4d587b2ec401eecbe506127aa0b5f742e2fdc46352a46a3ef5cde20243d3e6` (63) |
| `terminates_of_stepRespects_of_closureCriterion` | closure-criterion-sound-model: result | `Classical.choice`, `Quot.sound`, `propext` | `17a40a297dd90c8f93b6ce5d7c0abfd3042ee0a39473bdfe64707dc35e8b4887` | `f03ecb030df4d5fa8439d288467301d376355b4da7570a556dd2819b119de37c` (33) |

### Primary sources for prior art

Each record states how it was checked. Records marked "full text arXiv ... consulted" were checked only against the arXiv version; where no DOI is given, none was confirmed.

- [P1] C. S. Lee, N. D. Jones, A. M. Ben-Amram, "The size-change principle for program termination", POPL 2001, pp. 81-92, doi:10.1145/360204.360210 (bibliographic data verified via Crossref; statements checked in the full text). Definition 11: a program is size-change terminating if every infinite call sequence following its control flow has an infinitely descending thread. Theorem 1: size-change termination implies termination, for size-change graphs that are safe for the program and well-founded data. Theorem 4: the program is not size-change terminating iff the composition closure contains an idempotent G : f -> f with no strict arc x -> x; the forward direction is proved with Ramsey's theorem. Theorems 3 and 5: decidable in polynomial space; PSPACE-hard.
- [P2] A. Krauss, "Certified size-change termination", CADE-21, LNCS 4603, pp. 460-475, 2007, doi:10.1007/978-3-540-73595-3_34 (verified via Crossref and the publisher's abstract: a formalization of the size-change principle in Isabelle/HOL, used to construct certified termination proofs automatically). The full text was not consulted; no claim is made here about its proof route.
- [P3] A. M. Ben-Amram, "Size-change termination, monotonicity constraints and ranking functions", Logical Methods in Computer Science 6(3:2), 2010, doi:10.2168/LMCS-6(3:2)2010 (verified via Crossref; full text arXiv:1005.0253v5 consulted). Lemma 3.4: size-change termination implies semantic termination. Lemma 3.7 and Theorem 3.8: a monotonicity-constraint system terminates iff it is size-change terminating; the converse direction builds a satisfying assignment in a well-ordered set constructed in the proof (not necessarily the naturals). Section 4.3 warns that once the closure is reduced by subsumption, testing only idempotent graphs is incorrect.
- [P4] S. Steila, "An intuitionistic analysis of size-change termination", TYPES 2014, LIPIcs 39, pp. 288-307, 2015, doi:10.4230/LIPIcs.TYPES.2014.288 (verified at the publisher's page): the original proof of the size-change termination theorem used Ramsey's theorem for pairs; Vytiniotis, Coquand and Wahlstedt (2012) proved a classical variant intuitionistically via the Almost-Full Theorem; Steila gives an intuitionistic proof via the H-closure Theorem.
- [P5] D. Vytiniotis, T. Coquand, D. Wahlstedt, "Stop when you are almost-full: adventures in constructive termination", Interactive Theorem Proving (ITP 2012), pp. 250-265, doi:10.1007/978-3-642-32347-8_17 (DOI verified via Crossref; title and pages as listed in the references of Steila 2015; content as summarized by Steila 2015).
- [P6] A. M. Ben-Amram, C. S. Lee, "Ranking functions for size-change termination II", Logical Methods in Computer Science 5(2), 2009 (full text arXiv:0903.4382v4 consulted). Section 2.2: for a set G of size-change graphs over a well-ordered set of values, the transition system T_G (a state may move to any state that some graph of G describes; runStep here) terminates iff G satisfies SCT (Theorem 1, the 'only if' direction credited to Lee, TOPLAS 2009), and G satisfies SCT iff every idempotent graph of the composition closure has a strict self-arc (Theorem 2). Section 1: Lee (TOPLAS 2009) shows every terminating SCT instance has a global ranking function of the form min(max S_1, max S_2, ...), each S_i a set of lexicographically ordered tuples of variables and constants.
- [P7] J. Wright, L. Cohen, R. N. S. Rowe, A. Popescu, "Certified Infinite Descent Criteria in Isabelle/HOL", ITP 2026, LIPIcs 382, pp. 14:1-14:18, doi:10.4230/LIPIcs.ITP.2026.14, and the Archive of Formal Proofs entry "Certified Infinite Descent Criteria" (Infinite_Descent_Criteria, June 2026) (verified at the publisher's page and the AFP entry page): an Isabelle/HOL framework for Infinite Descent, the condition underlying size-change termination, with mechanized complete criteria (among them a relation-based criterion), soundness proofs of incomplete heuristics, and verified counterexamples certifying their incompleteness.
- [P8] C. A. Munoz, M. Ayala-Rincon, M. M. Moscato, A. M. Dutle, A. J. Narkawicz, A. A. Almeida, A. B. Avelar, T. M. Ferreira Ramos, "Formal verification of termination criteria for first-order recursive functions", ITP 2021, LIPIcs 193, pp. 27:1-27:17, doi:10.4230/LIPIcs.ITP.2021.27 (full text consulted; an extended version appeared in the Journal of Automated Reasoning 67(4), 2023): a PVS mechanization, for a first-order language, of the equivalence of semantic termination, measure termination, the size-change principle, calling context graphs and matrix-weighted graphs. Its Lemma 42 bounds the length of the circuits that must be checked by |W_p| * 3^(N^2) + 1 by a counting argument on (vertex, weight) pairs; this bound drives a fuel-bounded decision procedure (Dutle's procedure), the analogue of closureFuel here.
- [P9] R. Thiemann, J. Giesl, "The size-change principle and dependency pairs for termination of term rewriting", AAECC 16(4):229-270, 2005, doi:10.1007/s00200-005-0179-7 (verified via Crossref and the publisher's abstract): the size-change principle adapted to term rewriting.
- [P10] A. M. Ben-Amram, "General size-change termination and lexicographic descent", in The Essence of Computation, LNCS 2566, pp. 3-17, 2002, doi:10.1007/3-540-36377-7_1 (verified via Crossref and the publisher's abstract): size-change termination extends and subsumes lexicographic descent; the functions computable by size-change-terminating programs are exactly the multiply-recursive functions.
- [P11] C. S. Lee, "Ranking functions for size-change termination", ACM TOPLAS 31(3), 2009, doi:10.1145/1498926.1498928 (verified via the Crossref abstract; its completeness and ranking-function results are as summarized by Ben-Amram and Lee 2009, Sections 1 and 2.2).
- [P12] S. Steila, "An intuitionistic analysis of size-change termination", TYPES 2014, LIPIcs 39, pp. 288-307, 2015, doi:10.4230/LIPIcs.TYPES.2014.288 (full text consulted). Example 37 (Section 6): f(x, y) := if x > y then x else f(x + 1, y) is not SCT, since its only graph is idempotent with no decreasing edge, yet it terminates. Section 1 attributes to Heizmann, Jones and Podelski ("Size-change termination and transition invariants", SAS 2010, pp. 22-50) the result that size-change termination is strictly stronger than termination.
- [P13] A. M. Ben-Amram, "Size-change termination with difference constraints", ACM TOPLAS 30(3), Article 16, 2008, doi:10.1145/1353445.1353450 (verified via the Crossref abstract): with general difference bounds the analogous termination problem is undecidable; with at most one bound per target variable it is PSPACE-complete. Cited as context only.
- [P14] Lean 4 v4.34.1 sources (github.com/leanprover/lean4 at tag v4.34.1, files fetched and read): the termination_by docstring in src/Lean/Parser/Term.lean ('If omitted, a termination measure will be inferred') and the module documentation of src/Lean/Elab/PreDefinition/WF/GuessLex.lean (inference searches lexicographic combinations of basic measures sizeOf x_i, of measures e2 - e1 when e1 < e2 is found in the context of a recursive call, and of orders on the functions themselves for mutual recursion). The module documentation credits the search for lexicographic orders to Bulwahn, Krauss and Nipkow, "Finding lexicographic orders for termination proofs in Isabelle/HOL", TPHOLs 2007, pp. 38-53, doi:10.1007/978-3-540-74591-4_5 (verified via Crossref), and the idea of the measures e2 - e1 to Manolios and Vroon, "Termination analysis with calling context graphs", CAV 2006, LNCS 4144, pp. 401-414, doi:10.1007/11817963_36. Lean builds such definitions by well-founded recursion on a measure; it does not use the size-change principle. Checked with Lean v4.34.1: 'def swapF (x y : Nat) : Nat := if x = 0 then 0 else swapF y (x - 1)' is rejected with 'Could not find a decreasing measure' and accepted with 'termination_by x + y'; the Ackermann function is accepted with inferred measure (x1, x2); 'if x < 100 then f (x + 1) else 0' is accepted.
- [P15] Lee, Jones and Ben-Amram (POPL 2001, doi:10.1145/360204.360210), full text: Examples 3 (Ackermann, lexically ordered parameters), 4 and 5 (permuted parameters) in Section 1.4; Section 2.3.3 says Examples 4 and 5 'seem to possess no natural lexical descent'; Appendix B (more on related work, term rewriting) says size-change termination 'naturally subsumes an interesting class of orderings, including the lexical ordering'. These are informal remarks; no lexicographic statement is proved there.
- [P16] A. M. Ben-Amram, "General size-change termination and lexicographic descent", in The Essence of Computation, LNCS 2566, pp. 3-17, 2002, doi:10.1007/3-540-36377-7_1 (verified via Crossref and the publisher's abstract): size-change termination extends and subsumes lexicographic descent; the functions computable by size-change-terminating programs are exactly the multiply-recursive functions. Its lexicographic descent is tested along cycles of the call graph, not on every single call as LexProjDecreases requires.
- [P17] A. Abel, T. Altenkirch, "A predicative analysis of structural recursion", Journal of Functional Programming 12(1):1-41, 2002, doi:10.1017/S0956796801004191 (verified via the Crossref abstract: the foetus checker for structural recursion and a proof that structurally recursive terms normalize). Lee, Jones and Ben-Amram (POPL 2001, Section 5) describe foetus as returning a lexical ordering on the arguments if one exists.
- [P18] F. P. Ramsey, "On a problem of formal logic", Proceedings of the London Mathematical Society s2-30(1):264-286, 1930, doi:10.1112/plms/s2-30.1.264 (verified via Crossref).
- [P19] Isabelle/HOL library theory HOL-Library.Ramsey, section 'Ramsey's Theorem: Infinitary Version', theorem Ramsey (verified on the Isabelle library web page): a mechanized infinite Ramsey theorem.
- [P20] E. Frittaion, S. Steila, K. Yokoyama, "The strength of the SCT criterion", TAMC 2017, LNCS 10185, pp. 260-273 (full text arXiv:1611.05176 consulted): over RCA_0 the statement of the SCT criterion is equivalent to Sigma^0_2 induction; its classical proof needs only a 'triangle' corollary of Ramsey's theorem for pairs (infinitely many monochromatic triangles sharing a vertex).

### Toolchain

- Lean 4 `v4.34.1`, repository `leanprover/lean4`, tag commit `5045d0056413266e57c625dcd7c365b10e377c52` (tag object fetched from the GitHub API on 2026-11-20; the same commit is printed by `lean --version` of the toolchain used for every check). Core library only; no Mathlib; `lean/lakefile.toml` declares one `[[lean_lib]]` (`Toy`) and no `[[require]]`.

### Sources for the modeling bridge (Applicability)

Fetched and read on 2026-11-20:

- [B1] Agda 2.9.0, Haddock documentation of module `Agda.Termination.Termination` (https://hackage.haskell.org/package/Agda-2.9.0/docs/Agda-Termination-Termination.html): "Termination checker, based on 'A Predicative Analysis of Structural Recursion' by Andreas Abel and Thorsten Altenkirch (JFP'01), and 'The Size-Change Principle for Program Termination' by Chin Soon Lee, Neil Jones, and Amir Ben-Amram (POPL'01)"; "The termination criterion is taken from Jones et al. In the completed call graph, each idempotent call-matrix from a function to itself must have a decreasing argument. Idempotency is wrt. matrix multiplication." The user documentation page "Termination Checking" (https://agda.readthedocs.io/en/latest/language/termination-checking.html, Agda 2.10.0 documentation) describes structural recursion with lexicographic descent and the option `--termination-depth` ("termination depth N can track decrease up to N and increase up to N-1").
- [B2] Isabelle/Isar Reference Manual source, repository `isabelle-prover/mirror-isabelle`, file `src/Doc/Isar_Ref/HOL_Specific.thy` at its latest commit `446d51f954e2f91b8656d4fee8412f702103611b` (description of method `size_change`): "also works on termination goals, using a variation of the size-change principle, together with a graph decomposition technique ... Three kinds of orders are used internally: max, min, and ms (multiset) ... The search for a termination proof uses SAT solving internally."
- [B3] ACL2 community books, repository `acl2/acl2`, file `books/acl2s/ccg/ccg.lisp` at its latest commit `79fb1487b53cc49a59b31f8bc5b7b7a7ad32cf4b`: a calling-context-graph (CCG) termination analysis whose output includes "Size-change analysis has proven ... SCCs of the CCG terminating" (function `accg-sct-list1`). Calling context graphs are introduced in Manolios and Vroon, "Termination analysis with calling context graphs", CAV 2006, LNCS 4144, pp. 401-414, doi:10.1007/11817963_36 (title, authors and DOI as credited in [B4]; venue and pages as in [P14]).
- [B4] Lean 4 sources at tag `v4.34.1` (commit above): `src/Lean/Elab/PreDefinition/WF/GuessLex.lean`, module documentation ("This module finds lexicographic termination measures for well-founded recursion"; orders on the functions themselves for mutual recursion; credits Bulwahn, Krauss and Nipkow, doi:10.1007/978-3-540-74591-4_5, and Manolios and Vroon), and `src/Lean/Parser/Term.lean`, docstring of `termination_by` ("If omitted, a termination measure will be inferred").

### Lean termination-inference observations

Run on 2026-11-20 with Lean `v4.34.1` (commit above); the probe files are preserved in `support/lean_inference_probes/`:

- `SwapRejected.lean` (`def swapF (x y : Nat) : Nat := if x = 0 then 0 else swapF y (x - 1)`): rejected, "Could not find a decreasing measure."
- `Accepted.lean`, with `set_option showInferredTerminationBy true`: `swapF2` with `termination_by x + y` accepted; Ackermann accepted with "Inferred termination measure: termination_by x1 x2 => (x1, x2)"; `countUp` (`if x < 100 then countUp (x + 1) else 0`) accepted with "Inferred termination measure: termination_by 100 - x".

### Verification status of citations

Bibliographic records [P1]–[P20] state how each was checked when the result cards were written (Crossref, publisher page, full text, or arXiv only). On 2026-11-20, the DOIs of [P1] (doi:10.1145/360204.360210), [P2] (doi:10.1007/978-3-540-73595-3_34) and [P11] (doi:10.1145/1498926.1498928) were re-resolved through the Crossref API (titles and pages as recorded), and the DOIs used as `REPORT.json` subjects for Ramsey (1930, doi:10.1112/plms/s2-30.1.264), Ben-Amram (2010, doi:10.2168/LMCS-6(3:2)2010) and Steila (2015, doi:10.4230/LIPIcs.TYPES.2014.288) were re-checked against web search results pointing to the publishers' pages (Oxford University Press, episciences.org, Dagstuhl). Crossref requests for the other DOIs could not be completed from the checking environment on that date; those records rest on the verification stated in each record. Records without a DOI (Ben-Amram and Lee, LMCS 2009; Frittaion, Steila and Yokoyama, TAMC 2017; Heizmann, Jones and Podelski, SAS 2010) are cited from the arXiv full text or from citing papers, as stated in their records.

## Revalidation

Requirements: `elan` (so that `lake` and `lean` use the toolchain pinned in `lean/lean-toolchain`, `leanprover/lean4:v4.34.1`) and `python3`. No network access is needed after the toolchain is installed.

**Primary check.** From the package directory:

```sh
python3 support/revalidate.py .
```

It copies `lean/` to a temporary directory (the package is not modified) and checks: (1) `lake build` succeeds (this also runs `Toy/SCT/Audit.lean`, which fails on `sorryAx` or a non-standard axiom); (2) no Lean source contains `sorry`, `admit`, `native_decide` or an `axiom` declaration; (3) every declaration of the library depends only on `propext`, `Classical.choice`, `Quot.sound` (via `Lean.collectAxioms`); (4) for every name in `audit/statements.json` and every Lean name in the structured name fields of `results.json` (`lean`, `nonvacuity_witness_lean`, `positive_control_lean`, hypothesis `counterexample`s; names cited only in prose are not hashed and are covered by check (3)), the SHA-256 of `repr` of its type, and of its definition closure (sorted lines `name : repr type := repr value` for every library constant reachable from the type through types and definition bodies, theorem bodies excluded), equal the recorded values. It prints `REVALIDATED` on success. A changed hash means the statement or a definition it depends on changed, so the corresponding card must be re-examined.

**Manual equivalent.** The same audit as a package-included Lean program, `lean/RevalidationAudit.lean` (outside the `Toy` library target), which prints `#print axioms` for every declaration named in a result card's structured Lean fields and one line `REVALIDATION_AUDIT_JSON {...}` with each statement and closure:

```sh
cd lean
lake build
lake env lean RevalidationAudit.lean > /tmp/sct_audit.out
python3 - <<'EOF'
import hashlib, json, re
out = open('/tmp/sct_audit.out').read()
audit = json.loads(re.search(r'REVALIDATION_AUDIT_JSON (\{.*\})', out).group(1))
rec = json.load(open('../audit/statements.json'))['statements']
bad = [s['name'] for s in audit['stmts'] if rec.get(s['name']) != {
    'statement_sha256': hashlib.sha256(s['type_repr'].encode()).hexdigest(),
    'closure_sha256': hashlib.sha256('\n'.join(s['closure']).encode()).hexdigest(),
    'closure_size': len(s['closure'])}]
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
badax = [d['name'] for d in audit['decls'] if set(d['axioms']) - allowed]
print('hashed:', len(audit['stmts']), 'mismatches:', bad, 'non-standard axioms:', badax)
EOF
```

**Lean-inference observations** (Applicability and the `sct-not-lex`, `lex-implies-closure-criterion` and `sct-incomplete-for-termination` bridges) are re-run with:

```sh
cd support/lean_inference_probes
lean SwapRejected.lean    # expected: error "Could not find a decreasing measure."
lean Accepted.lean        # expected: no errors; prints the inferred measures
```

These probes establish only the behaviour of the pinned Lean release on these three definitions. The modeling-bridge statements about Agda, Isabelle and ACL2 rest on the documentation and source excerpts quoted under Evidence and must be re-read at a newer revision; no executable check of those tools is included.

