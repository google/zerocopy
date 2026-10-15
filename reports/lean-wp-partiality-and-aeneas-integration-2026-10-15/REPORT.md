# Lean WP, partiality and Aeneas integration at the October 2026 pins

## Summary

Lean now supplies generic weakest-precondition interfaces, verification-condition generation for monadic and deeply embedded programs, generalized framing, order-theoretic partial definitions, and independent checking tools. These facilities overlap with several layers of Aeneas's Lean libraries. They do not define Rust execution or establish the correspondence between Rust and generated Lean.

The current Aeneas backend differs materially from the older corpus snapshot: Result is an irreducible definition wrapping an interaction tree, not a three-constructor inductive. Its spec uses a least-fixed-point total-correctness predicate; dspec uses a greatest-fixed-point partial-correctness predicate. A legacy Std.Do bridge already exists, but that does not establish compatibility with every newer Std.WP interface or general Rust effect.

For TCB accounting, the decisive boundary is how a result enters a checked proof. At Lean 4.35.0, nativeEqTrue compiles a closed Boolean, evaluates it, and adds a fresh axiom asserting its result. A verified certificate algorithm executed through this route still has a native-evaluation trust obligation. The pinned Lake checker separately rejects nonstandard reachable axioms.

## Applicability

This report covers A26, A27 and A29 in #3886, with related implications for A28/A30.

Directly inspected subjects:

- AeneasVerif/aeneas at 21345f80fa212c596f6437378d7d57984fa2ea77; its Lean toolchain file selects v4.35.0-rc4.
- Released Lean 4.35.0 at eb6cafb7290e8bd5f2937522d8d804f58f02bafc.
- Lean master at 88539871b4133140b0d5e9beb4cd446bcc0d2f40 was used as a reconnaissance comparison, not substituted for the released source below.
- Versioned release documentation and the current manual where explicitly identified.

These are separate subjects. No build established that Aeneas's rc4 package works unchanged with released 4.35.0 or master. The source comparison itself already exposes naming/interface changes between release and master, such as WP.wpTrans versus later aliases. No Lean installation, proof execution, compiler benchmark or lake check run was performed for this package.

## Findings

### Three proof roles that must remain separate

1. A WP interpretation gives a program an assertion-transformer meaning.
2. Automation decomposes a goal about that interpretation and builds proof terms.
3. An adequacy or correspondence theorem relates that interpretation to the execution whose correctness is being claimed.

Lean supplies machinery for the first two roles and laws that support the third for particular monads. Rust-to-model correspondence remains another theorem. Merely registering a custom WP instance does not make it an adequate semantics: monotonicity alone is compatible with an interpretation that says True for every program and postcondition.

This is a derived observation from the class fields, not a defect in Lean. Applications choose a semantics and prove the extra laws their claims require.

### Std.WP is more general than a monadic VCG

At the release pin, Std.WP.Basic defines WP with a program type, value type, assertion lattice and exception assertion type. The class supplies wpTrans and monotonicity. A monad is one instantiation; a deeply embedded command datatype is another.

The release's tests/elab/vcgenImp.lean demonstrates a command AST with an environment-indexed WP, registered equations and vcgen proofs. This establishes the shape of an integration example in source. It does not prove an arbitrary command language adequate: the user-supplied WP and any independent operational semantics still need a relation.

Std.WP.Monad.Sound makes a further distinction explicit. LawfulWPMonadAttach relates a WP-provable postcondition to every value represented by MonadAttach.CanReturn. Its specialized of_run_eq_wp lemmas turn concrete run equations into value-level facts. Those theorems do not, merely by their names, establish that a computation terminates.

The exception interpretation is part of the specification. A postcondition on successful return and a permissive exception postcondition can establish a different property from Aeneas's success-only spec. A sound adapter must choose the error and divergence policy explicitly.

Basis: source; derived distinction between monotonicity, monadic laws and adequacy.

### Generalized framing supports spatial assertions, not an automatic Rust memory model

Std.WP.Frame defines a guarded framing property for a program and resource operator. Its frame-closure construction internalizes preservation under a family of resource operators; exception assertions receive a companion operator.

The vcgenSepLogic test demonstrates points-to, separating conjunction, magic wand and an allocation resource in a custom heap model. It verifies linked-list and stack examples over that model. The concrete heap is an address-to-optional-natural mapping; loads supply a default for missing cells, and loops in the described demonstrations are fuel bounded.

Consequently, the example is evidence that generalized framing and proof automation can be instantiated with a spatial assertion algebra. It is not an implementation of Rust provenance, value validity, lifetime borrowing, weak memory or full Iris. Those require semantic definitions and sound rules for the relevant source language.

The reusable integration seam is precise: define the program's WP from the chosen semantics, prove primitive and framing specifications, and register justified rules for automation. A frame procedure must produce proof evidence for its decomposition; successful heuristic matching cannot replace that evidence.

Basis: source and derived semantic-domain comparison.

### Current Aeneas Result and its two specification predicates

In Std/Primitives.lean:

- RustEffect.Input has a fail constructor carrying Error.
- Its result type is PEmpty, so the current effect has no successful response.
- Result is defined as ITree RustEffect, deliberately irreducible outside its implementation.
- Result.ok, vis, fail and div are interface operations; a MatchResult view supports case analysis.
- bind delegates to ITree.bind.

This representation can support a generic interaction-tree theory while preserving a compact public interface. It must not be described as unchanged from older inductive Result implementations.

In Std/WP.lean, effectWP maps the current failure effect to False. spec is DWP at unit state; dspec is DWLP at unit state. The two predicates differ on divergence:

| Current model value | spec | dspec |
| --- | --- | --- |
| ok a | postcondition at a | postcondition at a |
| fail e | False | False |
| div | False | True |

DWP uses the least fixed point of FunctionalWP with divergence forbidden. DWLP uses the greatest fixed point with divergence permitted. Their library proves total-to-partial implication, rules for bind and return, induction/coinduction principles and explicit divergence lemmas. Total correctness can exclude silent infinite computation; partial correctness deliberately does not.

The current RustEffect only contains failure. Generic effects in the interaction-tree library are not evidence that Aeneas extraction presently models arbitrary I/O, allocation events, concurrency or unsafe memory.

Basis: source.

### Existing Std.Do bridge and its limitations

The final part of Aeneas Std/WP.lean already registers Result.instWP and Result.instWPMonad using the older Std.Do interfaces. Its exception shape distinguishes:

1. modeled failure;
2. an otherwise-unhandled effect slot;
3. divergence.

The implementation comments restrict the current bridge to failure and divergence. Result.of_wp recovers a proposition about the entire Result value after all outcome cases are specified.

spec_to_mvcgen lifts a total Aeneas specification to a Std.Do triple. dspec_to_mvcgen requires an explicit precondition excluding div. That additional premise is a concrete example of why partial and total specifications cannot be interchanged based on similar notation.

Released Lean 4.35.0 deprecates mvcgen in favor of vcgen. The source bridge is still a useful starting point, but this investigation did not establish a drop-in migration or an adapter for all effect extensions. An appropriate compatibility experiment would compile an exact generated function and prove equivalence between the two chosen triples, including fail and div cases.

Basis: source, versioned release documentation.

### Partial definitions: logical equations and runtime behavior

There are several distinct mechanisms:

| Mechanism | Logical use | Obligation to retain |
| --- | --- | --- |
| Structural/well-founded recursion | A total function with its justified equations | Establish the chosen decreasing argument and identify runtime realization separately. |
| partial | Executable recursive definition, opaque to ordinary logical unfolding | It does not by itself provide usable semantic equations. |
| partial_fixpoint | Justified fixed-point equations under the relevant order/monotonicity construction | Identify the result order and the meaning of bottom or an unconstrained result. |
| Explicit fuel/evaluation relation | Termination bounded by fuel or related to a derivation | Prove adequacy and quantify fuel appropriately. |
| Interaction-tree semantics | Distinguishes return, visible effects and divergence | Choose total or liberal WP and prove source correspondence. |
| Coinductive predicates | Supports divergence/trace properties | Ensure the selected order and coinduction rule match the intended predicate. |

A tail-recursive equation returning an inhabited ordinary type may have several total logical solutions on a nonterminating execution. An equation such as f n = f (n+1) alone cannot certify a particular operational result or rule out divergence. A partiality-domain interpretation and an adequacy theorem can carry more information.

The release's vcgenCoinductiveFixpoint test records a concrete interaction: importing/opening the WP order infrastructure affects elaboration of mixed inductive/coinductive mutual definitions. The source contains both successful examples and guard_msgs rejection examples. This is an exact compatibility limitation at that pin, not a claim that coinduction and vcgen cannot generally coexist.

Basis: source, Lean recursive-definition documentation, derived distinction about equation underdetermination.

### Automation reuse: what must be proved before it helps

- grind and arithmetic solvers can discharge generated propositions once those propositions correctly encode Rust behavior.
- BitVec and fixed-width integer libraries supply mathematical operations and lemmas; Rust checked overflow, shifts, target usize and panic policies still need explicit correspondence.
- do notation and Lean loops can express target-side computation without duplicating all syntax plumbing. They do not justify source borrow ending or ownership erasure.
- Existing container specifications can help verify implementation algorithms. Their logical value types need not be the correct models of Rust allocation or layout.
- Quotation and Lean.Expr can construct output and proof terms, but the checked theorem must still identify the actual generated declaration.
- Aeneas's specialized step interface and total/partial specifications provide existing user-facing behavior. Replacing notation or tactics without relating their specifications could silently weaken a claim.

These are derived integration conditions grounded in the source interfaces, not measured assertions of reduced code size or faster proofs.

### Native evaluation and independent checking

Lean.Meta.Native.nativeEqTrue at the release pin:

1. requires a closed Boolean expression without free/metavariables;
2. creates and compiles an auxiliary declaration;
3. evaluates it as native code;
4. if true, adds a fresh axiom asserting the Boolean equality and returns that axiom as evidence.

Lean.Elab.Tactic.Decide uses this path for native_decide. The infrastructure also identifies bv_decide as a consumer. An external SAT solver can remain outside the logical trust boundary when a sound checker validates its certificate, while the execution of that checker still requires a trustworthy evaluation route. These are separate obligations.

The pinned Lake CLI Check.standardAxioms permits propext, Classical.choice and Quot.sound. checkUsedAxioms rejects reachable axioms outside that list. Thus a theorem depending on one of the fresh native-evaluation axioms would fail that particular policy. This is a consequence of the inspected implementations, not an observed run.

The same Check module supports exported proof checking, theorem comparison and optional bundled kernels. Its source lists leanchecker-paranoid, lean4lean, nanoda, con-leche and con-ron for paranoid checking. The release documentation describes sandboxed checking and a Linux-only sandbox limitation. Installed availability and agreement on a real Aeneas development were not tested here.

Independent checking helps detect invalid proof artifacts or unintended assumptions. It does not check that a Rust model is adequate or that an independently accepted theorem states the desired claim.

## Boundaries

- Not examined by execution: any new Lean build, generated Aeneas program, vcgen benchmark, independent kernel run or native-evaluation counterexample.
- Unknown: exact compatibility of the Aeneas rc4 package with released/master APIs; performance on ownership-heavy source proofs; adequacy of any new Rust WP instance.
- Known not to apply: promoting the minimal heap demonstration to Rust semantics, treating generic ITree effects as implemented Rust effects, or equating a custom WP instance with source adequacy.
- Older corpus reports about an inductive Result remain about their identified releases. Their claims should not be retroactively attached to this pin.
- No claim of an axiom-free complete Aeneas backend is made; dependency auditing requires compiled artifacts.

## Evidence

All source below is pinned:

- Aeneas at 21345f80fa212c596f6437378d7d57984fa2ea77: [Primitives.lean](https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/backends/lean/Aeneas/Std/Primitives.lean), RustEffect, Result and MatchResult; [WP.lean](https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/backends/lean/Aeneas/Std/WP.lean), spec/dspec and Result.instWP/spec_to_mvcgen/dspec_to_mvcgen.
- The same Aeneas pin: Data/Coinductive/ITreeWP/{DWP,DWLP,Taxonomy}.lean, fixed-point definitions and total/partial relation; lean-toolchain, v4.35.0-rc4.
- Lean at eb6cafb7290e8bd5f2937522d8d804f58f02bafc: [Std/WP/Basic.lean](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/Std/WP/Basic.lean), WP fields; Std/WP/Monad/Sound.lean, LawfulWPMonadAttach/of_run_eq_wp; Std/WP/Frame.lean, guarded framing and frame closure.
- The same release pin: tests/elab/{vcgenImp,vcgenSepLogic,vcgenCoinductiveFixpoint}.lean, concrete integration tests and their source limitations.
- [Lean.Meta.Native](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/Lean/Meta/Native.lean), nativeEqTrue; Lean/Elab/Tactic/Decide.lean, native_decide integration.
- [Lake CLI Check](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/lake/Lake/CLI/Check.lean), standardAxioms, checkUsedAxioms, bundledKernels and runCheck.
- [Lean 4.35.0 release notes](https://lean-lang.org/doc/reference/latest/releases/v4.35.0/), the documented vcgen/checking feature set.
- [Recursive definitions manual](https://lean-lang.org/doc/reference/latest/Definitions/Recursive-Definitions/), consulted 2026-10-15; its moving URL is explanatory evidence, not a replacement for pinned source.

The source-reading inventory records exact upstream blob IDs and selected symbols. No complete upstream source mirror is included.

## Revalidation

1. Pin the exact Aeneas backend and its required Lean toolchain; inspect Result and spec/dspec first.
2. Diff the relevant WP class fields and bridges before assuming compatibility with a new Lean release.
3. Compile a narrow generated-function example and prove the adapter's outcome cases, including failure and divergence, on a separately prepared execution surface.
4. Run primitive and frame-procedure specifications against the chosen Rust semantics; passing generic heap tests is insufficient.
5. Export the actual theorem and inspect its dependency axioms; run the selected independent-checking policy and preserve exact outputs.
6. Re-run the mixed fixed-point compatibility example if its namespaces/orders are needed.
7. Benchmark proof production and kernel checking separately before making scaling claims.

*Authored by an AI agent acting on joshlf's behalf.*
