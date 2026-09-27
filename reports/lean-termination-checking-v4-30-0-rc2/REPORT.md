# Lean termination checking at v4.30.0-rc2

## Summary

At `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (`v4.30.0-rc2`), ordinary recursive `def`/`theorem` elaboration does not add a primitive recursive constant to the kernel and then trust a separate termination verdict. Lean's elaborator instead rewrites accepted recursion into a non-recursive kernel term. It first tries structural recursion unless syntax forces another route; if structural recursion does not work, it can translate the definition through a well-founded fixpoint whose recursive calls require proofs that a measure decreases. The kernel then checks the resulting declaration in the ordinary way.

`termination_by` controls the measure or selects structural recursion. A non-structural `termination_by` forces the well-founded path; `termination_by structural ...` selects the structural path and requires the measure to be one of the function parameters. `decreasing_by` supplies tactics for the well-founded decrease obligations and also forces well-founded recursion. When neither is supplied, Lean first attempts structural recursion and then well-founded recursion with an inferred lexicographic measure. The inference machinery considers eligible parameters, `sizeOf`-based measures, certain context-derived natural-number differences, and function-order components for mutual recursion; every recursive call still has to satisfy the resulting decrease relation.

The important trust distinction is between finding a termination argument and checking the term that argument produces. Structural and well-founded termination search live in the elaborator and may use tactics and temporary local axioms while constructing a candidate term. The temporary axioms are installed under `withoutModifyingEnv` and are not retained. The accepted logical declaration is built from inductive recursors or `WellFounded.fix`/`WellFounded.Nat.fix` plus proof terms. Thus a buggy termination-search tactic should normally produce either a kernel-rejected term or a valid proof term, not silently authorize an arbitrary recursive logical definition. The separate `debug.skipKernelTC` option remains a global exception to that normal guarantee and is covered by the existing Lean trust report.

`unsafe`, `partial`, and the newer `partial_fixpoint`/lattice-fixpoint mechanisms are separate cases. Ordinary termination hints are unused on `unsafe` or `partial` definitions. This report records that boundary but does not characterize partial definitions or partial fixpoints in detail; those are separate #3720 subjects.

No fresh Lean execution was performed. The report uses exact pinned Lean source plus checked-in failure-test input/output as preserved upstream evidence.

## Applicability

The findings apply to Lean `v4.30.0-rc2` at commit `3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`, the release selected by current Anneal and by the pinned Aeneas Lean toolchain represented elsewhere in this corpus. They describe the ordinary recursive-definition elaboration machinery in `Lean.Elab.PreDefinition` and the core well-founded-recursion library it targets.

The report distinguishes three layers:

1. **surface termination hints** such as `termination_by`, `termination_by?`, and `decreasing_by`;
2. **elaborator transformations and search**, which choose a structural or well-founded encoding and construct proof terms; and
3. **kernel-visible declarations**, which contain the transformed non-recursive term rather than an unchecked "termination succeeded" bit.

The implementation also creates compiler-oriented recursive realizations after constructing accepted logical definitions. Those realizations belong to executable-code behavior, not to the kernel proof that the logical definition is well formed. This report identifies that split but does not prove semantic equivalence between the logical and compiled realizations.

Adjacent Lean releases are not assumed to behave identically. In particular, termination inference, generated helper structure, tactics, diagnostics, and partial-fixpoint support are implementation-sensitive.

## Findings

### Recursive predefinitions are partitioned into call-graph cliques before termination processing

`Lean.Elab.addPreDefinitions` first cleans the elaborated predefinitions, beta-reduces relevant local-recursive applications, and partitions mutually dependent definitions into strongly connected components. A singleton that does not mention itself is handled as non-recursive. Recursive cliques then take one of several paths based on declaration modifiers and termination hints.

For an ordinary safe recursive clique, `addPreDefinitions` checks the termination-hint consistency, elaborates any explicit measures, and chooses structural recursion, partial-fixpoint processing, or well-founded recursion. With no forcing hint, it combines errors from a structural attempt followed by a well-founded attempt.

This means "Lean checks termination" is not one monolithic algorithm. It is a dispatcher over different encodings whose output must be an ordinary kernel term.

Basis: **source** in `Lean/Elab/PreDefinition/Main.lean`.

### `termination_by` is a measure selection mechanism, and `structural` explicitly selects the structural route

The parser documentation at this revision states that ordinary `termination_by <term>` selects a termination measure and normally causes well-founded recursion. `termination_by structural <parameter>` instead asks Lean to use structural recursion. The structural measure must elaborate to one of the function parameters; `TerminationMeasure.elab` enforces that constraint.

`termination_by?` does not itself provide a measure. It asks the successful termination machinery to suggest the inferred measure. Structural processing can report the chosen recursive argument, while `GuessLex` can report the inferred well-founded measure.

For a mutually recursive clique, termination hints must be compatible. In particular, a clique cannot mix structural and non-structural `termination_by` annotations, and a `decreasing_by` clause is rejected as incompatible with structural recursion. Explicit termination measures for mutual well-founded recursion must also have compatible codomains.

Basis: **source** in `Lean/Parser/Term.lean`, `Lean/Elab/PreDefinition/TerminationHint.lean`, `Lean/Elab/PreDefinition/TerminationMeasure.lean`, `Lean/Elab/PreDefinition/Main.lean`, and `Lean/Elab/PreDefinition/WF/Rel.lean`.

### Structural recursion is accepted by translating recursive calls through an inductive recursor

The structural path searches for recursive arguments whose types belong to suitable inductive groups. Candidate arguments must satisfy concrete restrictions: for example, the argument must be non-fixed and inductive, and indexed inductive families must have usable variable indices with dependency constraints that permit the transformation. An explicit `termination_by structural ...` narrows this search to the requested parameter and turns an unsuitable choice into an error rather than silently choosing another argument.

Once a candidate set succeeds, `Structural.elimMutualRecursion` rewrites the recursive clique around the inductive group's `brecOn` machinery. `structuralRecursion` then installs the transformed declarations with `addNonRec`. The accepted logical declaration is therefore a non-recursive term built from inductive recursion principles rather than the original self-reference.

During this transformation, Lean temporarily adds the recursive functions as axioms so meta-level operations such as type inference and definitional equality can inspect expressions that still mention the not-yet-defined constants. The helper `withRecFunsAsAxioms` runs under `withoutModifyingEnv`; its own documentation explicitly says the environment is restored afterward. These temporary axioms are an elaboration device, not retained assumptions in the finished environment.

Basis: **source** in `Lean/Elab/PreDefinition/Structural/Main.lean` and `Lean/Elab/PreDefinition/Structural/FindRecArg.lean`.

### Well-founded recursion turns every recursive call into a call guarded by a decrease proof

The well-founded path first packs mutual recursion into a unary representation and preprocesses it. It then obtains a termination measure either from explicit `termination_by` clauses or from `GuessLex`. `WF.elabWFRel` synthesizes a `WellFoundedRelation` for the measure's codomain and lifts it back to the packed argument type with `invImage`.

`WF.mkFix` builds the recursive function with a well-founded fixpoint. If the relation is recognized as a natural-number less-than measure, it uses `WellFounded.Nat.fix`; otherwise it uses `WellFounded.fix` with the relation and its well-foundedness proof. While rewriting the body, each recursive application receives a proof obligation saying the callee argument is smaller than the caller argument under the selected relation.

`solveDecreasingGoals` then discharges those obligations. With an explicit `decreasing_by`, it runs the supplied tactic over the generated goals. Without one, it runs the default `decreasing_tactic`. Unsolved goals are reported rather than being accepted as termination evidence.

The core library makes the semantic contract explicit: `WellFoundedRelation α` contains both a relation and a proof that the relation is well founded; `invImage` preserves well-foundedness through a measure; `Nat.lt_wfRel` provides the standard natural-number order; and `WellFounded.Nat.fix` requires recursive calls to provide evidence that the new measure is smaller.

Basis: **source** in `Lean/Elab/PreDefinition/WF/Main.lean`, `Lean/Elab/PreDefinition/WF/Fix.lean`, `Lean/Elab/PreDefinition/WF/Rel.lean`, and `Init/WF.lean`.

### Automatic well-founded inference guesses a measure; it does not waive the decrease obligations

When the definition reaches the well-founded path without an explicit `termination_by`, `WF.guessLex` searches for a lexicographic measure. Its module documentation describes the strategy directly:

- start with basic measures derived from eligible parameters, using the parameter itself or `sizeOf` as appropriate;
- add certain natural-number measures derived from inequalities visible at recursive-call sites, such as differences of the form `e₂ - e₁` when the context contains a suitable comparison;
- for mutual recursion, consider function-order components as well as argument measures;
- try combinations until all recursive calls are lexicographically decreasing;
- use the explicit `decreasing_by` tactic if present, otherwise the default `decreasing_tactic`, to establish the candidate relations.

The combination search is deliberately bounded: `generateCombinations?` defaults to a threshold of 32 generated argument-measure combinations. Failure to infer a useful measure is therefore not evidence that no termination proof exists; it means this inference procedure did not find one. The error directs the user to provide `termination_by` explicitly.

The checked-in `tests/elab_fail/decreasing_by.lean` and its expected output preserve representative failures. The expected diagnostics show the inferred-measure matrix and the message `Could not find a decreasing measure`, and explicit but incomplete `decreasing_by` scripts leave unsolved proof goals.

Basis: **source** plus a checked-in upstream test fixture/expected-output artifact in `Lean/Elab/PreDefinition/WF/GuessLex.lean` and `tests/elab_fail/decreasing_by.lean*`. No fresh **execution** was performed for this report.

### The kernel checks the transformed declaration, not the elaborator's search result as an oracle

Both successful routes construct ordinary expressions before the declaration is added. The structural route creates a term based on recursors. The well-founded route creates a term based on `WellFounded.fix` or `WellFounded.Nat.fix` and proof arguments. `PreDefinition.Basic.addNonRec` constructs the corresponding theorem, opaque declaration, or definition and passes it through the ordinary declaration machinery.

This keeps termination search outside the trusted logical kernel in the important sense: the elaborator may choose a bad recursive argument, synthesize a bad measure, or run an unsound tactic, but the resulting declaration still needs to typecheck as an ordinary Lean term. A tactic that proves a false decrease goal only by introducing `sorry` or another axiom leaves that assumption in the proof term and is governed by the admission mechanisms documented in `lean-trust-admissions-v4-30-0-rc2`. Likewise, enabling `debug.skipKernelTC` changes the trust story globally; this report assumes the normal setting in which kernel checking is not skipped.

The structural implementation's temporary recursive axioms do not contradict this property because `withRecFunsAsAxioms` restores the environment before publication of the resulting declaration.

Basis: **source** + **derived** from the transformation and declaration paths, together with the separately published trust report for admission and kernel-check bypass behavior.

### Logical recursion and compiled recursive execution are represented separately

After installing the structurally or well-founded logical definition, the implementation invokes `addAndCompilePartialRec` for the original recursive predefinitions. `PreDefinition.Basic` creates compiler-oriented recursive declarations under an internal unsafe-recursive name with `DefinitionSafety.partial`; later realization machinery connects compilation to those artifacts.

For proof reasoning, the kernel-visible accepted definition is the structurally or well-founded transformed term. For native execution, Lean may use the recursive compiler realization instead. This is a concrete reason to keep logical termination soundness separate from executable-code equivalence. The source inspected here establishes the two representations and their construction order; it does not by itself prove that every compiled realization is semantically equivalent to the logical definition.

Basis: **source** in `Lean/Elab/PreDefinition/Structural/Main.lean`, `Lean/Elab/PreDefinition/WF/Main.lean`, and `Lean/Elab/PreDefinition/Basic.lean`, plus **derived** trust-boundary interpretation.

### `unsafe` and `partial` recursive definitions bypass ordinary termination checking by design

`addPreDefinitions` checks `unsafe` and `partial` modifiers before the ordinary termination machinery. Unsafe recursive definitions go through `addAndCompileUnsafe`; partial ones go through `addAndCompilePartial`. Their termination hints are reported as unused. They therefore must not be treated as evidence that Lean proved totality.

This does not mean such declarations can be used interchangeably with ordinary safe logical definitions. Lean tracks declaration safety, and the existing trust report records the boundary between safe declarations and unsafe executable code. `partial` and the separate `partial_fixpoint`/inductive-fixpoint/coinductive-fixpoint machinery have additional semantics outside this report.

Basis: **source** in `Lean/Elab/PreDefinition/Main.lean`, `Lean/Elab/PreDefinition/TerminationHint.lean`, and `Lean/Elab/PreDefinition/Basic.lean`.

### Error recovery can leave sorried or partial placeholders after a termination error, but that is not successful termination

If ordinary termination processing throws, `addPreDefinitions` logs the exception and then tries to add recovery declarations so elaboration can continue and later diagnostics remain useful. For ordinary definitions it may compile a partial recovery declaration whose logical body uses a synthetic `sorry`; for theorems it can call `addSorried` directly.

The prior logged error remains. These recovery declarations therefore cannot be used as evidence that the original recursive command passed termination checking. An external verifier that cares about a clean build must distinguish successful declaration elaboration from declarations present only after error recovery, and it must separately audit `sorry`/axiom dependencies if admissions are disallowed.

Basis: **source** in `Lean/Elab/PreDefinition/Main.lean` plus the existing Lean admissions report.

## Boundaries

- **No fresh execution was performed.** The report reconstructs the pinned behavior from implementation source and checked-in test artifacts. It does not claim a newly executed acceptance matrix.
- **Partial definitions are not characterized here.** `partial`, `partial_fixpoint`, `inductive_fixpoint`, and `coinductive_fixpoint` are separate mechanisms and separate #3720 subjects. This report records only where ordinary termination checking stops applying.
- **The automatic search is not complete.** Failure of structural inference or `GuessLex` does not establish mathematical nontermination. A user can provide a different valid measure or proof that the search did not discover.
- **A successful tactic is not automatically axiom-free.** `decreasing_by` produces proof terms through the tactic framework. Whether those terms depend on `sorry`, explicit axioms, native-evaluation assumptions, or other admitted facts is a separate trust audit.
- **Kernel checking is assumed.** The existing trust report documents `debug.skipKernelTC`; enabling it invalidates the ordinary "elaborator output is checked by the kernel" boundary.
- **Compiled-code equivalence is not proved here.** The source shows distinct logical and compiler-oriented recursive representations. This report does not establish that native execution of every accepted recursive definition refines the logical definition.
- **No complexity guarantee is claimed.** `GuessLex` has explicit search bounds and tactic-dependent work. This report records the algorithmic shape, not performance on large generated definitions.
- **No adjacent-version continuity is claimed.** Lean's termination elaborator is substantial implementation code and can change between releases.

## Evidence

**Primary Lean revision:** `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (`v4.30.0-rc2`).

- `src/Lean/Parser/Term.lean`, blob `16b73a52ad5c2e6819a9d009012a5e2d75f30559`: built-in documentation and parser syntax for `termination_by`, `termination_by?`, `decreasing_by`, and partial-fixpoint clauses.
- `src/Lean/Elab/PreDefinition/Main.lean`, blob `3d2169aeae3d4d29e04ba9421ec3b7f95ee799e7`: recursive-clique dispatch, hint consistency, structural-versus-well-founded fallback, unsafe/partial bypass, and error recovery.
- `src/Lean/Elab/PreDefinition/TerminationHint.lean`, blob `5448856c9a227fb37367aac1eedeafe220c11ef5`: elaborated hint representation, incompatibility rules, and unused-hint diagnostics.
- `src/Lean/Elab/PreDefinition/TerminationMeasure.lean`, blob `bd9b520513d877501adeae20d62fcc4f3cea7498`: explicit-measure elaboration and enforcement of structural-parameter measures.
- `src/Lean/Elab/PreDefinition/Structural/Main.lean`, blob `d3c72b3eb9b0d0d89d70294bf33ee0927ed9159f`: temporary recursive axioms, structural elimination through recursors, accepted non-recursive declarations, and compiler realization setup.
- `src/Lean/Elab/PreDefinition/Structural/FindRecArg.lean`, blob `92802d16417547323bf279e1163ba27d7e43eaf9`: structural recursive-argument eligibility and explicit-measure handling.
- `src/Lean/Elab/PreDefinition/WF/Main.lean`, blob `b066ac285ee76cf41a76275750f26810af9ece78`: mutual packing, measure selection, well-founded relation construction, fixpoint translation, and publication of the resulting declarations.
- `src/Lean/Elab/PreDefinition/WF/Fix.lean`, blob `0fef8a9aac176ae7941d8928d61df69b96dfa6a1`: recursive-call replacement, generated decrease obligations, tactic execution, and construction of `WellFounded.fix`/`WellFounded.Nat.fix` applications.
- `src/Lean/Elab/PreDefinition/WF/Rel.lean`, blob `f544ddbecffcecee378ff9284fe6270ee34d028b`: termination-measure codomain checks and construction of an inverse-image `WellFoundedRelation`.
- `src/Lean/Elab/PreDefinition/WF/GuessLex.lean`, blob `84e988dd16e89196f29a4f8f4c3cbafdb9700739`: automatic measure candidates, proof attempts, lexicographic search, mutual-function ordering, search bound, reporting, and failure diagnostics.
- `src/Lean/Elab/PreDefinition/Basic.lean`, blob `885df3685fdee44bf095924d951eb345dc8eb1f2`: construction of ordinary declarations and partial/unsafe compiler realizations.
- `src/Init/WF.lean`, blob `6225c703fef3bc62ded4f2e74c0df452ab5c977a`: `WellFoundedRelation`, `invImage`, natural-number well-foundedness, `sizeOfWFRel`, lexicographic product instances, and `WellFounded.Nat.fix`.
- `tests/elab_fail/decreasing_by.lean`, blob `1a58fc6f17db7064f8ccaf953d70a5915b883a68`, and `tests/elab_fail/decreasing_by.lean.out.expected`, blob `474a642aa87c8a7db571c293c870fcf035f3d50b`: checked-in examples of explicit and inferred well-founded measures, failed measure inference, and unsolved decrease goals.

**Related corpus evidence:** `reports/lean-trust-admissions-v4-30-0-rc2` at the current `google/zerocopy` `reference` branch documents `sorry`/axioms, safe-versus-unsafe declaration boundaries, executable-code trust, native evaluation, and `debug.skipKernelTC`. This report relies on that package only for the trust boundary around the generated termination proof term; it independently reconstructs termination elaboration itself.

Evidence roles are **source** and **derived**, with checked-in test input/output as preserved upstream test evidence. There is no fresh **execution** evidence from this run.

## Revalidation

For another Lean revision, the cheapest source-first revalidation is:

1. Diff `Lean/Elab/PreDefinition/Main.lean` to see whether the dispatch order among non-recursive, unsafe, partial, structural, partial-fixpoint, and well-founded definitions changed.
2. Diff `TerminationHint.lean` and `TerminationMeasure.lean` for syntax semantics, clique consistency, and structural-measure restrictions.
3. Diff `Structural/Main.lean` and `Structural/FindRecArg.lean` for the structural candidate rules and the term used to eliminate recursion.
4. Diff `WF/Main.lean`, `WF/Fix.lean`, `WF/Rel.lean`, and `WF/GuessLex.lean` for measure inference, generated decrease goals, default tactics, search bounds, and the final fixpoint term.
5. Diff `Init/WF.lean` for the well-founded relation/fixpoint primitives targeted by the elaborator.
6. Re-run the pinned `decreasing_by` failure tests and preserve their exact outputs.

On a capable execution surface, add a compact discriminating fixture with: one inferred structural recursion; one explicit `termination_by structural`; one explicit natural-number well-founded measure; one automatically inferred non-structural measure; one valid custom `decreasing_by`; one unsolved decrease obligation; one mutually recursive definition; and one `partial` control. Run it with `termination_by?` and `set_option showInferredTerminationBy true` where applicable. Preserve source, command line, Lean revision, stdout/stderr, and any generated declaration inspection. Separately run `#print axioms` on proof-bearing helpers if the goal is to establish admission-free termination proofs; successful termination elaboration alone does not establish that stronger property.