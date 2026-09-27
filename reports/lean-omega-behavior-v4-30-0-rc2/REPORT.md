# Lean `omega` behavior at v4.30.0-rc2

## Summary

At `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (`v4.30.0-rc2`), Lean's built-in `omega` tactic is a proof-producing arithmetic solver centered on integer and natural-number linear arithmetic. The user-facing tactic first turns the current goal into a contradiction problem, gathers the local hypotheses, translates supported arithmetic facts into integer linear constraints, and attempts to derive `False`. Its implementation follows the Omega-test family of algorithms: it normalizes and solves equalities, then eliminates variables from inequalities with Fourier–Motzkin-style real shadows.

The important limitation is explicit in the pinned source: this implementation does not implement the Omega algorithm's dark or grey shadows. It therefore is **not a complete decision procedure**. When the real-shadow elimination cannot derive a contradiction, `omega` may fail even when the arithmetic context is inconsistent. Failure is not evidence that the context is satisfiable or that the goal is false.

`omega` accepts more than bare linear inequalities. Its frontend recognizes equalities, order relations, disequalities, divisibility, logical connectives, and selected `Nat`, `Int`, `Fin`, and `BitVec` structure. It also introduces sound auxiliary constraints for operations such as division and remainder by recognized constants. Four case-splitting features are enabled by default: context disjunctions, natural subtraction, `Int.natAbs`, and `min`/`max`. The tactic delays disjunction splitting until its non-branching arithmetic pass fails, then retries under the branches.

The arithmetic expression frontend is intentionally not a general nonlinear normalizer. It expands multiplication only when at least one factor has no variable coefficients in the current linear-combination representation; otherwise the whole product becomes an opaque atom. The source also records a TODO to identify multiplicative atoms modulo associativity and commutativity. Thus `omega` can reason linearly *about* opaque nonlinear terms when they occur consistently, but it does not establish general nonlinear relationships among them.

The inspected implementation constructs Lean proof terms for the constraints it derives and for the final contradiction. The user-facing tactic packages the often-large proof in an auxiliary theorem before assigning the goal. This report did not execute Lean or independently audit the axiom dependencies of every internal helper theorem, so it does not make a stronger claim about the complete trusted-computing-base footprint.

## Applicability

This report applies to Lean 4 commit `3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`, identified by the selected Anneal toolchain as `v4.30.0-rc2`.

It covers the built-in `omega` tactic implemented under `Lean.Elab.Tactic.Omega`, including:

- the user-facing tactic entry point and configuration;
- extraction of arithmetic facts from the local context;
- expression normalization into integer linear combinations;
- delayed disjunction splitting;
- the equality and inequality elimination strategy; and
- construction of proof terms for successful contradictions.

The findings are source-based at this exact revision. No fresh Lean build or tactic execution was performed. Adjacent Lean versions are separate subjects; source continuity is not assumed.

The public tactic documentation describes `omega` as handling integer and natural linear arithmetic. The implementation accepts some additional forms, such as `Fin` comparisons and facts generated from `BitVec.toNat`. These source-level extensions are reported here because they affect actual behavior at the pinned revision, but they should not be treated as a stable cross-version interface unless separately documented or revalidated.

## Findings

### The tactic reduces the goal to contradiction and uses the whole local context

The user-facing evaluator first tries `assumption`; if that does not close the goal, `omegaTactic` calls `falseOrByContra`. The conversion has the familiar contradiction-oriented shape documented in the `Omega.lean` module:

- a `False` goal is already in the required form;
- a goal `¬ P` introduces `P`;
- a goal `x ≠ y` introduces `x = y`; and
- another proposition `P` is replaced by `¬¬P`, introducing `¬P`.

After that conversion, the tactic reads all local hypotheses and runs the arithmetic solver over them. A successful run returns a proof of `False`; the outer tactic packages the resulting proof in an auxiliary theorem because these proofs are commonly large.

This means `omega` is not a transformation that directly normalizes only the target expression. It proves the target by showing that the target's negation is inconsistent with the local context.

Basis: **source** — `src/Lean/Elab/Tactic/Omega.lean` and `src/Lean/Elab/Tactic/Omega/Frontend.lean`, especially `omegaTactic`, `omega`, and `omegaImpl`.

### The public contract is linear `Nat`/`Int` arithmetic, while the frontend recognizes a wider set of fact shapes

The built-in tactic documentation promises handling for hypotheses such as `x = y`, `x < y`, `x ≤ y`, and `k ∣ x` over `Nat` or `Int`, together with their negations. The frontend's `MetaProblem.addFact` accepts a broader collection at this revision.

For arithmetic propositions it recognizes:

- equality over `Int`, `Nat`, and `Fin`;
- `≤`, `<`, `>`, and `≥` over `Int`, `Nat`, and `Fin`;
- disequality over `Int` and `Nat`;
- divisibility over `Int` and `Nat`; and
- negated supported propositions after `pushNot` transforms them.

It also decomposes or converts selected logical structure:

- implications are converted into a disjunctive form;
- conjunctions are split into both conjuncts;
- existential and subtype hypotheses contribute their witness property;
- equivalences are converted into a disjunction of the two consistent truth assignments; and
- disjunctions may be queued for later splitting.

Unsupported proposition shapes are ignored rather than automatically becoming arithmetic facts. In particular, a general dependent `forall` is rejected by this path unless it is recognized as a propositional arrow.

Basis: **source** — `src/Init/Tactics.lean` and `src/Lean/Elab/Tactic/Omega/Frontend.lean`, `MetaProblem.addFact`.

### Arithmetic is reflected into integer linear combinations, with unsupported nonlinear structure treated as atoms

The expression frontend translates ground integers, variables, addition, subtraction, and negation into `LinearCombo` values. Natural-number expressions are pushed toward integer arithmetic through explicit casts and accompanying facts such as non-negativity.

Multiplication has a precise boundary. The frontend recursively reflects both factors, but expands the product only when one factor's coefficient vector is zero. In that case, the multiplication remains linear because one side is constant with respect to the discovered atoms. If both sides contain atom coefficients, the implementation restores the reflection state and records the whole product as a new atom instead.

This boundary has two consequences:

1. `omega` can still use an expression such as `x * y` as an opaque variable in linear relations if the same expression recurs consistently.
2. It does not infer arbitrary nonlinear algebraic identities among such atoms. The module documentation specifically records a TODO to identify atoms modulo associativity and commutativity so that, for example, commuted products can be recognized as the same nonlinear atom.

The reflection cache and atom table canonicalize expressions sufficiently for the implementation's current equality tests, but they are not a polynomial normalization engine.

Basis: **source** — `src/Lean/Elab/Tactic/Omega/Frontend.lean`, `asLinearCombo`, `asLinearComboImpl`; `src/Lean/Elab/Tactic/Omega/OmegaM.lean`, `lookup`.

### Casts and selected arithmetic operations generate additional constraints

The frontend does more than flatten `+` and `-`. It rewrites or augments several forms so that useful linear facts become visible.

At this revision:

- a newly discovered `((x : Nat) : Int)` atom contributes non-negativity;
- a `Fin.val` or `BitVec.toNat` reached through such a cast can contribute its upper-bound fact;
- casts are pushed through selected natural arithmetic operations;
- division by a recognized positive constant creates an atom for the quotient and adds the standard quotient bounds;
- remainder is rewritten through integer remainder/division identities when the modulus is recognized;
- divisibility by a supported constant is reduced to a remainder-equals-zero fact;
- `Int.natAbs`, natural subtraction, `min`, and `max` can introduce facts or case splits according to configuration; and
- an integer-valued `if` expression can contribute the disjunction connecting the condition to the chosen branch.

The implementation's helpers `groundNat?` and `groundInt?` recognize some closed arithmetic expressions, not only a literal token. The public documentation describes the supported division, remainder, and divisibility cases conservatively in terms of literal constants; callers should not assume a broader stable contract without revalidation.

Basis: **source** — `src/Lean/Elab/Tactic/Omega/Frontend.lean`, `asLinearComboImpl`; `src/Lean/Elab/Tactic/Omega/OmegaM.lean`, `groundNat?`, `groundInt?`, `analyzeAtom`.

### Disjunctions are delayed until the straight-line arithmetic pass fails

`MetaProblem` keeps arithmetic facts and pending disjunctions separately. `omegaImpl` first processes all immediately usable facts and runs equality/inequality elimination without case-splitting the queued disjunctions. Only if the resulting problem remains possible does it call `splitDisjunction`.

The splitter takes one queued disjunction, tries the first branch, and recurses only when the branch contributes usable facts. If both branches are relevant, it proves `False` in both and combines the results with `Or.elim`. If a disjunction contributes no new arithmetic information, the implementation skips it and tries the next pending disjunction.

Natural subtraction and other special operations feed this same mechanism. The design therefore avoids eagerly multiplying the search space when the linear core already suffices, while retaining selected branch-sensitive arithmetic reasoning.

The configuration documentation warns that irrelevant disjunctions can nevertheless increase run time significantly because the implementation does not always know in advance whether a split will be useful.

Basis: **source** — `src/Lean/Elab/Tactic/Omega/Frontend.lean`, `MetaProblem`, `omegaImpl`, `splitDisjunction`; `src/Init/Meta/Defs.lean`, `OmegaConfig`.

### All four exposed case-splitting options are enabled by default

`OmegaConfig` defines four Boolean options, each defaulting to `true`:

- `splitDisjunctions`;
- `splitNatSub`;
- `splitNatAbs`; and
- `splitMinMax`.

The user-facing syntax accepts ordinary tactic configuration, for example the built-in documentation's `omega +splitDisjunctions +splitNatSub +splitNatAbs +splitMinMax`. Turning an option off removes that source of case splitting; it does not otherwise replace the core arithmetic algorithm.

The documentation calls out an important interaction: with `splitDisjunctions := false`, `omega` will often be unable to solve equality goals because contradiction setup can turn a disequality into the disjunction `x < y ∨ x > y`.

Basis: **source/documentation** — `src/Init/Meta/Defs.lean`, `OmegaConfig`; `src/Init/Tactics.lean`; `src/Lean/Elab/Tactic/Omega/Frontend.lean`, `evalOmega`.

### Equality solving is exact, but inequality elimination is deliberately incomplete

After reflection, `omega` normalizes integer constraints and solves equalities before attacking inequalities.

For equalities, it first eliminates variables with coefficient `±1`. If the remaining equality has only larger coefficients, the implementation introduces a balanced-modulo equality that creates a coefficient `±1`, then eliminates that variable. The module documentation explains the decreasing coefficient measure used to ensure this process terminates operationally.

For inequalities, `omega` chooses a variable and performs Fourier–Motzkin elimination. It prefers eliminations that introduce no new inequalities, then eliminations known to be exact, and otherwise minimizes the number of new constraints.

The incompleteness is explicit: the source implements only the **real shadow** of the Omega algorithm. It does not implement the dark or grey shadows required for a complete integer decision procedure. If real-shadow processing leaves a satisfiable-looking problem, `omega` must fail unless a queued disjunction provides another route to contradiction.

The source says exact elimination is available when all upper-bound coefficients or all lower-bound coefficients for the selected variable have unit magnitude. In those cases, omitting the dark and grey shadows loses nothing for that elimination. Outside those cases, a successful contradiction remains sound, but failure is inconclusive.

Basis: **source** — `src/Lean/Elab/Tactic/Omega.lean`; `src/Lean/Elab/Tactic/Omega/Core.lean`, especially equality solving, Fourier–Motzkin selection, and elimination.

### Success constructs a Lean proof; failure reports the residual arithmetic problem

The core associates each reflected constraint with a `Justification`. Derived constraints retain justification structure through normalization, combinations, equality elimination, and balanced-modulo steps. Once a contradiction is found, the implementation recursively turns that justification into Lean expressions proving the derived constraints and finally proves `False`.

The frontend then instantiates metavariables and returns the proof. The user-facing tactic hides the potentially large expression behind an auxiliary theorem before closing the goal.

When no contradiction is found and no useful disjunction remains, `omega` throws an error. If no usable arithmetic constraint was extracted, the diagnostic suggests unfolding definitions so that linear facts become visible. Otherwise it formats the remaining atoms and constraints to describe the problem it could not discharge.

This source path is evidence that the tactic produces proof terms rather than returning a bare Boolean solver result. It is not, by itself, an independent audit that every helper theorem is axiom-free or that no separately enabled Lean trust bypass affects kernel checking.

Basis: **source** — `src/Lean/Elab/Tactic/Omega/Core.lean`, `Justification.proof` and `Problem.proveFalse`; `src/Lean/Elab/Tactic/Omega/Frontend.lean`, `formatErrorMessage`, `omegaImpl`, and `omegaTactic`.

## Boundaries

- **No fresh execution was performed.** The report reconstructs behavior from exact pinned source and built-in source documentation. It does not preserve a newly run success/failure matrix or performance measurements.
- **`omega` is not complete at this revision.** The missing dark and grey shadows make failure inconclusive for integer arithmetic problems that need those parts of the Omega algorithm.
- **General nonlinear arithmetic is not supported.** Products with variable structure on both sides become atoms rather than expanded polynomial expressions. A repeated opaque atom can still participate in linear constraints, but algebraic relationships among distinct nonlinear forms are not established automatically.
- **Atom equivalence is limited.** The source explicitly records associativity/commutativity recognition of monomials as future work.
- **Definitions may need to be exposed.** The failure diagnostic itself recommends unfolding when arithmetic facts are hidden behind definitions. This report does not characterize the full reducibility/canonicalization boundary.
- **The source accepts more forms than the conservative public summary.** Source-level handling of `Fin`, `BitVec`, `if`, and closed arithmetic expressions may change without preserving a user-facing compatibility promise.
- **The proof dependency set was not independently audited.** The inspected code constructs proof terms from Lean lemmas. A separate `#print axioms` or declaration-dependency audit would be needed to establish a stronger statement about admissions or trusted assumptions.
- **No adjacent-version continuity is claimed.** Algorithm completeness, preprocessing, configuration, diagnostics, and accepted expression forms must be revalidated at a different Lean revision.

## Evidence

**Primary Lean revision:** `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (`v4.30.0-rc2`).

- `src/Lean/Elab/Tactic/Omega.lean`, blob `708d3657f2995a06b489e781f8739c80c7b7b8b1`: module-level algorithm description, preprocessing, equality solving, real/dark/grey shadow distinction, delayed disjunction strategy, explicit incompleteness, and future work.
- `src/Lean/Elab/Tactic/Omega/Frontend.lean`, blob `1c807cc35b4d67b3912df0945431e5fcfa4c8274`: proposition extraction, arithmetic reflection, casts, division/remainder rewrites, multiplication boundary, disjunction handling, diagnostics, contradiction setup, and user-facing tactic entry point.
- `src/Lean/Elab/Tactic/Omega/OmegaM.lean`, blob `74af59dfb59bc31e443ea60498d2ce7fe9c52c21`: atom canonicalization/state, closed-number recognition, and auxiliary facts for casts, quotient/remainder, `Fin`, `BitVec`, `min`/`max`, and `if`.
- `src/Lean/Elab/Tactic/Omega/Core.lean`, blob `68b9bfd0ef782c0ca264d6921b139f63ead97eeb`: constraint representation, justification-to-proof conversion, equality elimination, Fourier–Motzkin variable selection, and real-shadow elimination.
- `src/Init/Meta/Defs.lean`, blob `8a65ffcc70b918db1c7004b346df6de1dfff0334`: `OmegaConfig` and the default semantics of the four split controls.
- `src/Init/Tactics.lean`, blob `34366138005fb7460f0c6823c1393065b3128b35`: built-in user documentation for `omega`, its supported arithmetic surface, incompleteness, and configuration syntax.

The evidence roles are **source** and source-embedded **documentation**. The report's statements that follow from combining those implementation facts are **derived**. There is no fresh **execution** evidence in this package.

The implementation source cites William Pugh's “The Omega test: a fast and practical integer programming algorithm for dependence analysis” as the algorithmic reference. This report did not independently use the paper to extend the claims beyond what the pinned Lean implementation establishes.

## Revalidation

For another Lean revision, a cheap source-first revalidation is:

1. Diff `src/Lean/Elab/Tactic/Omega.lean` for the algorithm description, especially whether dark/grey shadows remain unimplemented and whether the preprocessing contract changed.
2. Diff `Frontend.lean` for accepted proposition forms, reflection rules, nonlinear multiplication handling, division/remainder rewrites, disjunction processing, and the tactic entry point.
3. Diff `OmegaM.lean` for atom canonicalization and automatically generated facts.
4. Diff `Core.lean` for equality elimination, variable selection, real-shadow elimination, and justification/proof construction.
5. Diff `src/Init/Meta/Defs.lean` and `src/Init/Tactics.lean` for configuration defaults and the public tactic contract.

On a surface with the exact Lean toolchain, add a compact behavioral fixture that records:

- a direct `Nat`/`Int` linear inequality proof;
- equality and disequality goals;
- divisibility plus constant division/remainder;
- natural subtraction that requires a split;
- `Int.natAbs` and `min`/`max` with each split option enabled and disabled;
- a repeated opaque nonlinear product that can be treated as one atom;
- two syntactically distinct nonlinear products whose relationship would require unsupported normalization;
- a no-usable-constraints failure; and
- an integer problem selected specifically to distinguish real-shadow success from a case that needs the missing dark/grey machinery.

Record the exact Lean revision, source, command line, stdout/stderr, and configuration. If the trust boundary matters, separately inspect the resulting theorem with Lean's declaration/axiom-reporting tools; tactic success alone does not establish the stronger admission-free claim.
