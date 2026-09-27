# Lean `omega` at v4.30.0-rc2

## Summary

At Lean `v4.30.0-rc2`, `omega` is a proof-producing tactic for contradictions in integer and natural-number arithmetic. The user-facing tactic first turns the goal into a contradiction problem with `false_or_by_contra`, then feeds every local hypothesis to an arithmetic frontend. That frontend recognizes a broader logical shell—such as conjunctions, implications, existentials, selected equalities and order relations, and optionally disjunctions—but ultimately extracts integer linear equalities and inequalities and asks the Omega implementation to prove them inconsistent.

The supported arithmetic surface is wider than "linear syntax" suggests. The frontend normalizes `Nat` and `Int` relations, pushes many `Nat`-to-`Int` coercions inward, reasons about division and remainder by suitable constants, splits natural subtraction and several other piecewise operations, and handles `Fin` order/equality through values. Multiplication is linearized only when one factor is already constant as a linear combination; otherwise the product is treated as an opaque atom. Repeated occurrences of definitionally equal atoms are canonicalized, but the source explicitly notes that algebraically equivalent monomials such as `a * b` and `b * a` are not generally identified.

`omega` is intentionally incomplete at this revision. Its implementation omits the Omega algorithm's dark and grey shadows. When a Fourier–Motzkin elimination is not exact, the tactic may therefore fail even though the arithmetic problem is inconsistent. Failure is not a counterexample proof: the error can print constraints that a possible counterexample may satisfy, but the source explicitly permits false negatives. Successful use, by contrast, constructs a contradiction proof from the processed hypotheses.

## Applicability

This report applies to `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`, released as `v4.30.0-rc2`, and specifically to the built-in `omega` frontend and Omega implementation at that revision.

The report covers the user-facing `omega` tactic, its default configuration, the logical and arithmetic forms recognized by its frontend, the main normalization and elimination strategy, important incompleteness boundaries, and control-flow behavior relevant to generated proof scripts.

It does not characterize `bv_omega`; the pinned test suite uses that separate tactic for `BitVec` examples. It also does not claim completeness for Presburger arithmetic, stable behavior across Lean revisions, or performance bounds for large generated goals.

No fresh Lean execution was performed. Checked-in tests are used as source evidence for intended behavior, not as execution evidence acquired by this report.

## Findings

### The user-facing tactic proves the goal by deriving `False` from all local hypotheses

`omegaTactic` calls `falseOrByContra` before invoking the arithmetic solver. For a `False` goal this leaves the goal unchanged; for negations and disequalities it introduces the positive proposition; for an ordinary proposition it turns the goal into a contradiction problem by introducing its negation.

After that transformation, the tactic collects all local hypotheses and passes them to `omega`. The solver constructs a proof of `False`; the frontend then closes the original goal. As a result, `omega` can close a non-arithmetic proposition when the local arithmetic context is inconsistent. The pinned tests include a goal such as an arbitrary `prime 10` proposition proved from contradictory natural-number hypotheses.

Before doing this work, `evalOmega` tries `assumption`. Thus an already available proof can close the goal without constructing an Omega proof.

Basis: **source**.

### The frontend recognizes a logical shell around `Nat`, `Int`, and `Fin` arithmetic

`MetaProblem.addFact` weak-head-normalizes a hypothesis type and recursively extracts supported facts. At this revision it directly handles:

- equality over `Int`, `Nat`, and `Fin`;
- `<`, `≤`, `>`, and `≥` over `Int`, `Nat`, and `Fin`;
- disequality over `Int` and `Nat`;
- divisibility over `Int` and `Nat`;
- negations that `pushNot` can transform into supported positive facts;
- proposition-valued arrows, by converting an implication into a disjunction;
- conjunctions, existentials, subtypes, iff statements, and `Prod.Lex`;
- disjunctions when `splitDisjunctions` is enabled.

Unsupported proposition shapes are ignored rather than treated as arithmetic facts. The frontend counts newly extracted facts and case-splits deferred disjunctions only when the current linear problem does not already produce a contradiction.

The checked-in `omega.lean` tests exercise these interfaces, including conjunctions, iff goals and hypotheses, implications, existentials, subtypes, `Prod.Lex`, `Fin`, and divisibility.

Basis: **source**.

### Arithmetic is reflected into integer linear combinations, with nonlinear subterms becoming atoms

The frontend represents arithmetic expressions as integer linear combinations over discovered atoms. Addition, subtraction, and negation compose linear combinations directly. Multiplication is expanded only when at least one factor's coefficient vector is zero—that is, when one factor is already a constant with respect to the current atom set. If both factors contain variables, the complete product becomes an atom.

This distinction explains why `omega` can still use hypotheses containing nonlinear-looking expressions when the same opaque product appears consistently, while it cannot generally reason about polynomial identities between differently shaped products. The top-level implementation notes a TODO to identify atoms modulo associativity and commutativity and gives `a * b` versus `b * a` as the motivating limitation. The pinned regression file likewise comments that some differently associated products are not solved.

Atoms are canonicalized up to definitional equality through `Lean.Meta.Canonicalizer`; this is stronger than raw syntax identity but weaker than algebraic normalization of arbitrary nonlinear expressions.

Basis: **source**.

### Natural-number and integer preprocessing exposes many common arithmetic forms

The pinned frontend contains targeted rewrites that turn common Lean arithmetic into the integer linear problem. Important cases include:

- `Nat` equality and order are cast to `Int`;
- strict order is converted to non-strict order with a unit offset;
- `Nat` casts are pushed through addition, multiplication, division, remainder, powers with suitable ground bases, and several projections;
- natural values contribute non-negativity facts;
- integer division by a suitable nonzero constant introduces quotient bounds;
- integer remainder is rewritten through division, with range facts added where applicable;
- divisibility is translated through remainder-equals-zero facts;
- `Fin` relations are translated through `Fin.val`;
- `Int.toNat`, selected shifts, `Int.natAbs`, `min`, and `max` have specialized preprocessing paths.

Natural subtraction is not treated as ordinary integer subtraction. When enabled, a cast of `(a - b : Nat)` contributes a disjunction distinguishing `b ≤ a`, where the subtraction agrees with integer subtraction, from `a < b`, where the natural subtraction is zero.

The exact set of rewrites is implementation-specific. Expressions outside these recognized forms may remain opaque atoms rather than being simplified algebraically.

Basis: **source**.

### Division, remainder, and divisibility support depends on recognizable constant structure

For integer division, `asLinearComboImpl` handles a denominator that `groundInt?` can evaluate. Division by zero is rewritten using the corresponding zero-division theorem; negative constant divisors are reduced to positive ones; positive constant division is then treated as an atom accompanied by quotient bounds.

Remainder similarly receives special treatment when the modulus is recognizable. The top-level documentation describes replacing division and remainder by a literal natural modulus with fresh-variable constraints, while `OmegaM.analyzeAtom` records range facts for several positive constant and power-of-constant shapes.

The test corpus contains examples using constant-denominator division, remainder, and divisibility. These examples should not be generalized to arbitrary symbolic divisors: when the denominator/modulus is not recognized by the pinned preprocessing, the expression can remain opaque and the solver may lack the relationship needed for a proof.

Basis: **source**.

### Four default-on configuration switches control case splitting and piecewise preprocessing

`OmegaConfig` has four Boolean fields at this revision, all defaulting to `true`:

- `splitDisjunctions`;
- `splitNatSub`;
- `splitNatAbs`;
- `splitMinMax`.

`splitDisjunctions := false` prevents the frontend from queueing `Or` hypotheses for case splitting. The source documentation warns that this also prevents many equality goals from being solved because contradiction conversion and negation processing often expose a disequality as an order disjunction.

The other three fields suppress the corresponding case analyses for natural subtraction, integer absolute value, and `min`/`max`. The pinned test suite contains examples that deliberately fail with one of these options disabled and succeed with the default configuration.

These switches affect completeness and search cost rather than merely diagnostics. In particular, disabling a split can remove facts required to derive the contradiction.

Basis: **source**.

### Disjunctions are deferred and split only after the current linear problem fails

The frontend stores supported disjunctions instead of splitting them immediately. It first processes all non-disjunctive facts and runs the linear solver. If that already finds a contradiction, no branch split is needed. Otherwise it takes a pending disjunction, recursively tries both branches, and constructs an `Or.elim` proof when both branches lead to `False`.

The top-level Omega documentation states that disjunctions are processed first-in, first-out and that inequality-elimination work must be redone in each branch, although equality-elimination work can be reused. It also notes that the implementation does not optimize split order.

For generated proofs, an irrelevant disjunction can therefore increase work substantially even when the arithmetic core is otherwise small. The `OmegaConfig` documentation explicitly warns about this performance effect.

Basis: **source**.

### The arithmetic core solves equalities first, then uses Fourier–Motzkin elimination

After preprocessing, the core maintains linear equality and inequality constraints over integer atoms. It normalizes constraints, solves equalities, and then eliminates variables from inequalities.

Equalities with a coefficient of `±1` directly eliminate a variable. Harder equalities are transformed using a balanced-modulus construction that introduces a new variable but reduces the coefficient measure until a unit coefficient becomes available.

For inequalities, `fourierMotzkinSelect` prefers an elimination that introduces no new constraints; otherwise it prefers an exact elimination, and then fewer generated constraints. An elimination is considered exact when all lower-bound coefficients or all upper-bound coefficients for the selected variable have absolute value one.

Basis: **source**.

### Missing dark and grey shadows make `omega` a one-sided prover, not a complete decision procedure

The implementation's own top-level documentation says that the dark and grey shadows from the Omega algorithm are not implemented. With those shadows absent, a non-exact Fourier–Motzkin real shadow can be satisfiable even when the original integer problem is not.

The implementation handles this conservatively: when elimination leaves a possible problem, it does not invent a contradiction. It tries deferred disjunctions and otherwise fails with `omega could not prove the goal`. Consequently, success establishes a constructed proof, but failure does not establish satisfiability or even the existence of a genuine counterexample.

This is a material boundary for generated proof search. Replacing a successful `omega` call with a logically equivalent but differently presented arithmetic problem can move it outside the tactic's incomplete solving envelope even when the theorem remains true.

Basis: **source**.

### Failure diagnostics describe a possible constraint model, not a certified counterexample

When no usable arithmetic constraints are extracted, the error says so and suggests unfolding definitions so that arithmetic facts become visible. When constraints remain possible after elimination, the formatter prints them and says that “a possible counterexample may satisfy the constraints,” together with names for the remaining atoms.

The wording is deliberately noncommittal. Because the solver may have dropped information through an inexact real-shadow elimination and because opaque atoms need not be independently realizable, the displayed assignment constraints are not a certified model of the original Lean proposition.

The pinned test file checks the shape of several such error messages, including the no-usable-constraints case.

Basis: **source**.

### The tactic may hide a large generated proof behind an auxiliary theorem

After `omega` fills a fresh metavariable with the contradiction proof, the frontend creates an auxiliary theorem with `mkAuxTheorem` and assigns that theorem to the original goal. The source comment explains the reason: Omega proofs are typically large.

This affects generated-source shape and debugging. A successful `omega` does not generally leave its full proof term inline in the tactic script's elaborated expression; Lean can introduce an auxiliary declaration to contain it.

Basis: **source**.

### A debug option can replace `omega` with `sorry`

`debug.terminalTacticsAsSorry` is a built-in Boolean option whose default is `false`. When it is enabled, `omegaTactic` admits the goal instead of running the arithmetic solver.

This is explicitly a debugging and bootstrapping facility, not ordinary Omega semantics. Nevertheless, a generated-proof environment that relies on `omega` for trusted checking should ensure this option is not enabled. A successful tactic invocation under that debug setting is not evidence that the arithmetic frontend or solver established the theorem.

Basis: **source**.

## Boundaries

No fresh Lean execution was performed. Checked-in examples establish what the pinned source tree intends to cover, but this package does not reproduce their runtime output independently.

The report does not characterize `bv_omega`. The main Omega test file contains a separate `BitVec` section that invokes `bv_omega`, which has its own preprocessing pipeline.

The report does not claim completeness for Presburger arithmetic. The pinned implementation explicitly omits dark and grey shadows, so valid goals can fail even when their arithmetic meaning lies within integer linear arithmetic.

The report does not treat arbitrary multiplication, division, modulus, powers, `min`/`max`, or casts as fully normalized arithmetic. Only the concrete pinned preprocessing paths described above are established; unsupported shapes can survive as opaque atoms.

The report does not claim that a printed “possible counterexample” is a model of the original Lean goal.

The report does not give performance bounds. Source comments identify potentially expensive disjunction splitting and constraint growth, and checked-in benchmark files exist, but no fresh benchmark was run here.

The report does not generalize to adjacent Lean releases. Both the frontend's recognized expression forms and the arithmetic core are implementation details that can change.

## Evidence

**Subject.** `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (`v4.30.0-rc2`). Evidence was acquired on 2026-09-27.

Primary pinned **source**:

- `src/Lean/Elab/Tactic/Omega.lean`, blob `708d3657f2995a06b489e781f8739c80c7b7b8b1`: algorithm overview, preprocessing model, equality solving, Fourier–Motzkin elimination, explicit dark/grey-shadow incompleteness, disjunction strategy, and future-work limits.
- `src/Lean/Elab/Tactic/Omega/Frontend.lean`, blob `1c807cc35b4d67b3912df0945431e5fcfa4c8274`: arithmetic reflection, supported proposition shapes, `Nat`/`Int`/`Fin` conversion, piecewise preprocessing, disjunction handling, error formatting, contradiction conversion, user-facing tactic entry point, and auxiliary-theorem construction.
- `src/Lean/Elab/Tactic/Omega/Core.lean`, blob `68b9bfd0ef782c0ca264d6921b139f63ead97eeb`: normalized constraint representation, equality elimination, Fourier–Motzkin data selection, exactness criterion, and contradiction proof construction.
- `src/Lean/Elab/Tactic/Omega/OmegaM.lean`, blob `74af59dfb59bc31e443ea60498d2ce7fe9c52c21`: atom canonicalization, expression cache, and generated facts for casts, division/remainder, natural subtraction, `min`/`max`, and conditionals.
- `src/Init/Meta/Defs.lean`, blob `8a65ffcc70b918db1c7004b346df6de1dfff0334`: exact `OmegaConfig` fields and defaults.
- `src/Lean/Meta/Tactic/Util.lean`, blob `b583d6d0da51794fceeda6e78f95cfb8f0834316`: `debug.terminalTacticsAsSorry`, default `false`.
- `tests/elab/omega.lean`, blob `25b3e90e699c1ea473d1f43f2155c141664f26f0`: checked-in regression coverage for arithmetic forms, case splitting, failure cases, logical shells, `Fin`, configuration switches, and diagnostic output.
- `tests/elab/omega_examples.lean`, blob `8e6603435eea9fac680c74d9a7359154c1879e8d`: compact checked-in examples for inequalities, GCD constraints, natural subtraction, constant division, divisibility, remainder, equation systems, disjunctions, and duplicated hypotheses.

The release tag `v4.30.0-rc2` resolves to the same commit `3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`. There is no fresh **execution** evidence in this package.

## Revalidation

For another Lean revision, the cheapest reliable revalidation is source-first:

1. diff `src/Lean/Elab/Tactic/Omega.lean` for the documented algorithm, especially whether dark/grey shadows remain absent;
2. diff `Frontend.lean` for `asLinearComboImpl`, `MetaProblem.addFact`, disjunction splitting, `omegaTactic`, and error formatting;
3. diff `Core.lean` for equality elimination, `fourierMotzkinSelect`, and the exactness rule;
4. diff `OmegaM.lean` for atom canonicalization and generated facts;
5. diff `src/Init/Meta/Defs.lean` for `OmegaConfig`;
6. inspect `tests/elab/omega.lean` and `omega_examples.lean` for changed supported cases and changed known failures.

If any of those regions changed materially, run a small pinned probe that distinguishes at least:

- contradictory and satisfiable `Nat`/`Int` linear constraints;
- a hard integer equality whose GCD cannot divide the constant;
- natural subtraction with `splitNatSub` enabled and disabled;
- a disjunctive proof with `splitDisjunctions` enabled and disabled;
- constant-denominator division and remainder;
- a nonlinear product used as the same opaque atom versus algebraically rearranged products;
- a `Fin` comparison;
- a true proposition that the pinned implementation cannot prove because elimination is inexact;
- a no-usable-constraints failure and a remaining-constraints failure.

Preserve the exact Lean revision, probe source, command, output, and configuration. A passing probe covers only those examples; source inspection is still needed to re-establish the frontend's complete recognized-form set and the solver's incompleteness boundary.
