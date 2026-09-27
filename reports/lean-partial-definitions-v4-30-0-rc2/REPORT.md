# Lean partial definitions separate an opaque logical constant from recursive executable code

## Summary

At Lean `v4.30.0-rc2` (`leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`), `partial def` does not admit a nonterminating recursive body as the logical value of the user-visible declaration. Lean instead creates an **opaque logical declaration** with the requested type and an arbitrary inhabitant of that type, then separately creates a `DefinitionSafety.partial` recursive implementation named `<decl>._unsafe_rec` for code generation.

This split has two important consequences for Anneal. First, ordinary kernel reduction and definitional equality do not expose the recursive equations of a `partial def`. A checked-in Lean test confirms that `Kernel.whnf` leaves an application of a partial function stuck and that it is not definitionally equal to its computed result. Second, executable evaluation can still run the recursive implementation because the compiler deliberately prefers the `_unsafe_rec` declaration when one exists. Therefore a proposition proved only by ordinary kernel reasoning cannot silently obtain the operational equations of a `partial def`; proof mechanisms that trust compiled execution, such as `native_decide`, cross a separate execution trust boundary.

`partial def` is also different from `partial_fixpoint`. The former gives up a logical characterization of the recursive body and retains only an opaque inhabitant at the proof level. `partial_fixpoint` is a distinct elaboration route intended to justify a possibly nonterminating function through a lattice-theoretic fixed point and expose equations as theorems. These constructs should not be treated as interchangeable when auditing Anneal-generated proof code.

No fresh Lean execution was performed for this report. The findings come from exact pinned implementation source and checked-in Lean tests at the selected revision.

## Applicability

Anneal currently selects Lean `v4.30.0-rc2`, revision `3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`. This report answers the #3720 inventory item about partial definitions, irreducibility, and proof boundaries at that exact revision.

The result matters whenever generated or supporting Lean code contains `partial def`, invokes a partial definition from propositions, or uses executable proof procedures over expressions containing partial functions. It also gives a concrete rule for source review: the body written after `partial def` is primarily an executable implementation, not the logical value of the same-named constant.

This report complements the existing `lean-trust-admissions-v4-30-0-rc2` reference package. That package establishes the broader admission and compiled-execution boundaries. The present report narrows in on how `partial def` is elaborated and why its executable behavior is not available through ordinary definitional reduction.

## Findings

### `partial def` bypasses the ordinary termination elaborators

The recursive-definition dispatcher in [`Lean.Elab.PreDefinition.Main`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Lean/Elab/PreDefinition/Main.lean) handles explicit partial declarations before structural or well-founded recursion. When a recursive clique contains a `partial` modifier, Lean requires each partial declaration to have a function type and calls `addAndCompilePartial`. Termination hints are then reported as unused for a partial definition.

That means `partial def` is not “well-founded recursion with a missing proof.” It selects a different elaboration route. In particular, the structural-recursion and well-founded-recursion transformations described in the termination reference do not justify the source body.

Basis: **source**.

### The user-visible logical declaration is opaque and gets an arbitrary inhabitant

`addAndCompilePartial` does not install the recursive source body as the value of the user-visible declaration. For each partial predefinition it telescopes the declared type, calls `mkInhabitantFor`, changes the declaration kind to `opaque`, and passes that replacement value to `addNonRec`.

[`Lean.Elab.PreDefinition.MkInhabitant`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Lean/Elab/PreDefinition/MkInhabitant.lean) shows what this means. `mkInhabitantFor` attempts to synthesize an inhabitant of the result type, using `Inhabited`, `Nonempty`, function arguments, and unfolding of the result type. If it cannot establish nonemptiness, elaboration fails with a diagnostic saying that the partial definition could not be compiled because the type could not be proved nonempty.

The logical value therefore need not have any semantic connection to the source recursive body. Its job is to make a well-typed opaque logical constant available without asserting an arbitrary proposition. This is why the nonemptiness condition matters: Lean may choose an arbitrary value only when the result type is known to contain one.

Basis: **source**.

### The recursive source body is retained under `_unsafe_rec` for execution

After creating the opaque logical declarations, `addAndCompilePartial` calls `addAndCompilePartialRec`. [`Lean.Elab.PreDefinition.Basic`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Lean/Elab/PreDefinition/Basic.lean) rewrites the recursive clique so that each declaration is named `Compiler.mkUnsafeRecName preDef.declName`, replaces recursive references with those renamed declarations, and installs the resulting mutual definition with `DefinitionSafety.partial`.

At this revision, `Compiler.mkUnsafeRecName` appends `_unsafe_rec`. The checked-in [`tests/elab/partial1.lean.out.expected`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/tests/elab/partial1.lean.out.expected) makes the split concrete. For a local recursive loop inside `partial def reverse`, Lean prints:

- `opaque reverse.loop ...`
- `partial def reverse.loop._unsafe_rec ... :=` followed by the actual recursive implementation.

For the outer `reverse`, which is no longer recursive after the local loop is separated, Lean prints an ordinary definition that calls the opaque `reverse.loop` logically. The compiler can nevertheless recover the recursive executable implementation through the `_unsafe_rec` convention described below.

Basis: **source** + checked-in **execution** output.

### The compiler intentionally prefers `_unsafe_rec` over the opaque logical declaration

[`Lean.Compiler.LCNF.ToDecl`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Lean/Compiler/LCNF/ToDecl.lean) documents and implements the executable-side substitution. `getDeclInfo?` first looks up `mkUnsafeRecName declName` and only then falls back to the ordinary declaration. `toDecl` normalizes an `_unsafe_rec` input name back to the user-facing name before selecting declaration information, and its comment states that if a declaration has an unsafe-rec version, that version is used.

This is not a theorem that the opaque logical inhabitant equals the executable function. It is a compiler convention that supplies code for a declaration whose proof-level meaning is intentionally opaque and unrelated to those recursion equations.

Basis: **source**.

### Ordinary kernel reduction does not compute a partial definition

The checked-in [`tests/elab/kernel2.lean`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/tests/elab/kernel2.lean) defines a recursive `partial def fact`. It then creates `c3 := fact 10` and asks the kernel directly for weak-head normalization and definitional equality. The expected messages record:

- `c3 ==> fact ...` rather than the factorial result; and
- `c3 =?= v1 := false` even though `v1` is the numeral `3628800` that the executable function computes.

This is the behavior Anneal should assume for ordinary proof elaboration: the partial function's recursive equations are not available as definitional computation.

The result also sharpens the meaning of “irreducible” here. The user-visible recursive component is an `opaque` declaration, and ordinary kernel conversion does not expose its arbitrary inhabitant. This is not merely an elaborator reducibility attribute that a tactic can override to recover the source recursion equations; those equations live in the separate executable `_unsafe_rec` declaration.

Basis: checked-in **execution** output + **source**.

### A partial function can still execute, including inside native proof procedures

[`tests/elab/reduce1.lean`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/tests/elab/reduce1.lean) uses the same style of `partial def fact`. Ordinary `#guard` checks execute the function successfully, including `fact 100`. The same file proves equalities about the partial function with `by native_decide`.

This does not contradict the kernel-reduction result. Native evaluation goes through compiled code, where the compiler deliberately selects the `_unsafe_rec` implementation. The existing `lean-trust-admissions-v4-30-0-rc2` report establishes the additional trust step used by `native_decide`: compiled execution is observed and a fresh axiom is added for the successful Boolean result. Thus a theorem about a partial function can be obtained through native execution, but the theorem's trust story then includes that native-execution admission path rather than ordinary kernel reduction of the partial function.

Anneal should therefore distinguish two questions:

1. Can the logical kernel reduce or derive the source equations of a `partial def`? Not through the ordinary definitional behavior shown here.
2. Can trusted tooling execute the partial function and feed the result back into a proof? Yes, through mechanisms such as `native_decide`, with the larger trust boundary already documented in the admission report.

Basis: checked-in **execution** evidence + **source** + derived composition with the existing trust reference.

### `DefinitionSafety.partial` belongs to the executable auxiliary, not the user-facing opaque constant

[`Lean.Declaration`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Lean/Declaration.lean) gives definitions three safety states: `unsafe`, `safe`, and `partial`. `ConstantInfo.isPartial` is true only for a `defnInfo` whose safety is `.partial`. The recursive `_unsafe_rec` declaration is installed with exactly that state.

By contrast, `addAndCompilePartial` changes the user-visible recursive declaration into an `opaque` declaration. `OpaqueVal` carries only an `isUnsafe` Boolean; it has no `partial` safety state. The proof-facing and executable objects are consequently different declaration kinds as well as different values.

This distinction also matters across module boundaries. [`Lean.AddDecl`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Lean/AddDecl.lean) exports an opaque declaration through its opaque presentation, while definitions exported without their bodies use an axiom presentation. The logical interface of a partial function therefore remains the opaque user-facing constant rather than exporting the recursive body as a logical definition.

Basis: **source**.

### `partial def` and `partial_fixpoint` solve different problems

The parser documentation for `partial_fixpoint` describes it as defining a possibly nonterminating function as a fixed point in a suitable partial order. It says the function is compiled like a partial function **but its equations are provided as theorems**, subject to monotonicity conditions. That is a materially different proof interface from `partial def`, whose source recursion equations are absent from ordinary definitional equality.

The two mechanisms therefore should not be collapsed into a single “partial recursion” category in Anneal analysis. `partial def` is appropriate when executable behavior is needed without a proof-level equation story. `partial_fixpoint` is designed to retain a justified logical fixed-point characterization and deserves separate verification analysis.

Basis: **documentation** + **source**.

### Error recovery can also build a partial-shaped placeholder, but that is not successful `partial def` semantics

`Lean.Elab.PreDefinition.Main` has a recovery path after recursive-definition elaboration fails. For suitable declaration kinds it may call `addAndCompilePartial` with `useSorry := true` so later elaboration can continue. In that mode the opaque logical value is a labeled synthetic sorry rather than an inhabitant produced by `mkInhabitantFor`.

That recovery state follows an error. It should not be mistaken for successful acceptance of an ordinary recursive definition or for the normal semantics of explicit `partial def`. When analyzing a successful build, the relevant explicit-partial path uses the nonempty inhabitant route described above.

Basis: **source**.

## Boundaries

This report characterizes explicit `partial def` at the pinned Lean revision. It does not establish that every compiler backend implements every partial function correctly, nor that a diverging partial function has any particular runtime behavior beyond the ordinary language/runtime behavior of its generated code.

No fresh Lean process was run. Checked-in test files and expected output count as preserved execution evidence from the Lean repository, not as an independently reproduced experiment.

The report does not claim that the arbitrary opaque inhabitant is observable through normal proof reduction. The opposite is the relevant operational fact: checked-in kernel tests show that the partial function remains stuck under kernel WHNF and definitional equality. The inhabitant explains why the opaque declaration can be kernel checked, not a route for proving source recursion equations.

This report does not fully analyze `partial_fixpoint`, `inductive_fixpoint`, or `coinductive_fixpoint`; it uses their documented distinction only to delimit `partial def`. A separate report would be appropriate if Anneal intends to emit those constructs.

The report also does not repeat the complete `native_decide`, unsafe-declaration, `implemented_by`, or `debug.skipKernelTC` trust analysis. Those mechanisms are already covered by `lean-trust-admissions-v4-30-0-rc2`; the present report only composes that result with partial-definition execution where necessary.

## Evidence

Primary subject: `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (`v4.30.0-rc2`).

**Source** evidence:

- `src/Lean/Elab/PreDefinition/Main.lean` — explicit-partial dispatch; construction of an opaque logical declaration; error-recovery `useSorry` path.
- `src/Lean/Elab/PreDefinition/MkInhabitant.lean` — construction and failure conditions for the arbitrary inhabitant used as the opaque logical value.
- `src/Lean/Elab/PreDefinition/Basic.lean` — `_unsafe_rec` rewriting and creation of the `DefinitionSafety.partial` recursive executable declaration.
- `src/Lean/Declaration.lean` — `DefinitionSafety`, `OpaqueVal`, `ConstantInfo.isPartial`, and declaration representations.
- `src/Lean/Compiler/LCNF/ToDecl.lean` — code generation prefers `_unsafe_rec` and recognizes an opaque declaration with an `_unsafe_rec` companion as partial/unsafe for compiler purposes.
- `src/Lean/AddDecl.lean` — kernel checking and exported declaration presentations.
- `src/Lean/Parser/Term.lean` — documentation distinguishing `partial_fixpoint` from ordinary partial compilation and stating that fixed-point equations are available as theorems.

Preserved checked-in **execution** evidence:

- `tests/elab/partial1.lean` and `tests/elab/partial1.lean.out.expected` — printed opaque logical helper alongside its `partial def ... _unsafe_rec` implementation.
- `tests/elab/kernel2.lean` — kernel WHNF and definitional equality do not compute `partial def fact`.
- `tests/elab/reduce1.lean` — executable guards compute a partial factorial, and `native_decide` can prove propositions that depend on that executable behavior.

Existing corpus evidence used for composition:

- `reports/lean-trust-admissions-v4-30-0-rc2/` — native execution is a separate theorem-trust path; unsafe/safety and compiled implementation substitution are distinct from ordinary kernel reasoning.

There is no fresh **execution** evidence in this report.

## Revalidation

For a newer Lean revision, first inspect `Lean.Elab.PreDefinition.Main.addAndCompilePartial`, `Lean.Elab.PreDefinition.Basic.addAndCompilePartialRec`, `Lean.Elab.PreDefinition.MkInhabitant`, and `Lean.Compiler.LCNF.ToDecl.getDeclInfo?`. The central discriminator is whether Lean still creates two semantically different objects: an opaque proof-facing constant and a recursive executable companion selected by the compiler.

Then rerun the smallest behavioral probes represented by the checked-in tests:

1. define a simple terminating `partial def fact`;
2. inspect the user-facing declaration and its `_unsafe_rec` companion;
3. ask the kernel for WHNF of `fact 10` and definitional equality with `3628800`;
4. evaluate `fact 10` through ordinary executable evaluation; and
5. prove the equality with `native_decide`, then inspect its axiom dependencies.

If a future Lean version provides source equations for `partial def`, removes `_unsafe_rec`, changes how the compiler chooses implementations, or makes the user-visible declaration reducible, this report should be replaced rather than generalized across revisions.