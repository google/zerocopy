# Aeneas weakest-precondition and proof-tool interfaces at nightly-2026.06.03

## Summary

At `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`, the proof-facing interface is simpler than the phrase “generated weakest-precondition function” suggests. Aeneas translates a Rust function to a Lean function in the `Result` monad. A single generic predicate, `Aeneas.Std.WP.spec`, then states that this computation returns `.ok` and that its returned value satisfies a postcondition. Aeneas does not emit a separate WP definition or specification theorem for every translated Rust function.

That distinction matters because `spec` is a strong success predicate at this pin. `Result` has `ok`, `fail`, and `div` constructors, and `WP.spec m P` is false for both `fail` and `div`. For `ok x`, it reduces to `P x`. The library proves the exact equivalence `spec m P ↔ ∃ y, m = ok y ∧ P y`. A theorem written as `f x ⦃ y => Q y ⦄` therefore establishes successful termination of the translated `Result` computation plus `Q`; it is not merely partial correctness conditional on normal return.

The `step` tactic is theorem-directed symbolic proof automation over that interface. Theorems tagged `@[step]` describe calls as `Result` specifications. When a proof goal contains a monadic call, `step` finds or is given an applicable theorem, proves or exposes its preconditions, introduces the returned values and postcondition facts, and composes the theorem with the surrounding computation through `spec_bind'` or `spec_mono'`. `step*` repeats that process and explores branches; `step*?` additionally reconstructs an explicit proof script for inspection. These tactics do not add semantics beyond the Lean theorems they apply, and they can stop with unresolved goals when no theorem, instantiation, precondition proof, or terminal proof is available.

Mutable-borrow backward functions fit this same interface without a second WP mechanism. They are values in the successful `Result` payload, so a specification can bind both a forward result and one or more backward continuations and state properties of each. The proof layer is therefore generic over the functionalized values described in the separate Rust-to-Lean translation report.

Historical Anneal V1 built an additional “orthogonal WP” adapter on top of these upstream facts. Its `wp_prove_orthogonal` theorem split `WP.spec m P` into existence of a successful result and a correctness implication about any successful result. That split was an Anneal V1 proof interface, not an upstream Aeneas semantic rule and not current V2 design authority.

No fresh Lean, Aeneas, Charon, or Rust execution was performed. The report is based on exact pinned source, upstream documentation, checked-in Lean proof examples, and historical Anneal V1 source.

## Applicability

Primary subject:

- Aeneas repository: `AeneasVerif/aeneas`
- revision: `ac9f1bc5262a5e4ff1e24ca78617121382202727`
- release: `nightly-2026.06.03`
- Lean toolchain recorded by that revision: `leanprover/lean4:v4.30.0-rc2`
- Mathlib revision in the Aeneas Lean manifest: `5450b53e5ddc75d46418fabb605edbf36bd0beb6`

Current Anneal at `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9` selects the same Aeneas release and Lean version in `anneal/flake.nix`. Current Anneal design does not freeze the proof encoding or the Anneal/Aeneas boundary; this report records the upstream proof surface available to that design.

Historical Anneal V1 observations apply only to `anneal/v1/` at the identified zerocopy revision. V1 is used to explain an already-preserved integration pattern, not to prescribe V2 architecture.

In this report, “specification theorem” means a Lean theorem whose conclusion is an Aeneas `WP.spec` proposition, usually written with `⦃ ... ⦄` notation. “Generated function” means the Lean function emitted by Aeneas from a Rust/LLBC function. Those are separate artifacts at this pin.

## Findings

### `Result` distinguishes success, failure, and divergence before the WP layer

`Aeneas.Std.Result` is an inductive type with three constructors:

- `ok v` for successful return;
- `fail e` for modeled failure;
- `div` for divergence.

Its monadic `bind` calls the continuation only for `ok`; it propagates `fail` and `div` unchanged. Generated Lean can therefore retain a distinction between failure and divergence as values of the translated semantic datatype.

The basic WP success predicate deliberately collapses that distinction when asking whether a successful specification holds.

Basis: **source**.

### `WP.spec` means successful termination plus the postcondition

The WP library defines:

- `Post α := α → Prop`;
- `Pre := Prop`;
- `Wp α := Post α → Pre`;
- `wp_return x := fun p => p x`;
- `theta (ok x) := wp_return x`;
- `theta (fail _) := fun _ => False`;
- `theta div := fun _ => False`;
- `spec x p := theta x p`.

The accompanying theorems reduce `spec (ok x) P` to `P x` and reduce both failure forms to `False`. Most directly, `spec_equiv_exists` proves:

`spec m P ↔ ∃ y, m = ok y ∧ P y`.

Thus a successful proof of `spec m P` establishes that the translated computation has a concrete `ok` result and that the result satisfies `P`. It rules out both modeled failure and modeled divergence for that invocation.

This is a claim about the Aeneas functional model. Whether the model faithfully accounts for all Rust behaviors is a separate source-to-model question.

Basis: **source**.

### The `⦃ ... ⦄` notation is syntax for the same generic predicate

The Lean backend defines notation such as:

`f x ⦃ y => Q y ⦄`

by elaborating it to `Aeneas.Std.WP.spec (f x) (fun y => Q y)`. Multi-result notation is implemented by nested `uncurry`/`uncurry'` wrappers. Tuple patterns and multiple binders change how the successful payload is destructured; they do not define another verification semantics.

This is why a translated function whose successful value contains a forward result and a backward function can be specified as:

`choose b x y ⦃ z back => ... ⦄`.

The prior Rust-to-Lean translation report establishes why mutable-borrow translation places such backward functions in the returned value. This report establishes that the ordinary WP machinery simply quantifies over that composite value.

Basis: **source** + upstream **documentation**.

### Aeneas emits translated function definitions, not one generated WP theorem per Rust function

The extraction backend prints pure translated function declarations and their result types. The proof-facing WP predicate is supplied by the reusable Lean library. The checked-in proof documentation then has users write specification theorems such as:

`@[step] theorem my_function_spec ... : my_function x ⦃ r => ... ⦄ := by ...`.

The `@[step]` attribute registers such a theorem for automation; it does not identify an automatically generated specification that accompanies every extracted Rust function.

Aeneas does have narrower metaprogramming helpers that synthesize `step` theorems for pure Lean definitions. For example, `step_pure_def` generates a theorem with a `.step_spec`-style name and registers it. That helper is not a per-Rust-function specification ABI.

Consequently, code that wants a reusable semantic contract for an arbitrary translated function must establish a theorem for that function or rely on a theorem already provided by the Aeneas libraries. The generated Lean definition alone is executable/model code, not a proof that any particular postcondition holds.

Basis: **source** + upstream **documentation** + checked-in proof examples.

### A `@[step]` theorem has a stable proof role but not one mandatory theorem name

The `step` implementation documents the expected theorem shape as a function call under `spec`, with ordinary arguments and optional preconditions followed by a postcondition over one or more returned values. In schematic form:

`theorem thm ... (h₁ : pre₁) ... : f args ⦃ r₁ ... rₙ => post ⦄`.

The theorem name itself is not the lookup key. Registering the theorem with `@[step]` stores semantic matching data in the step database. The tactic can also bypass database selection with `step with theorem_name`.

For mutable-state translations, the returned binders can include backward functions. Their update behavior belongs in the postcondition just like any other property of the successful payload.

Basis: **source** + upstream **documentation**.

### `step` composes specifications through monadic binds

The central proof transformation uses `Std.WP.spec_bind'` when the current program position is a monadic let/bind and `spec_mono'` for the non-bind case.

`spec_bind'` has the logical shape:

1. establish a postcondition for the called computation;
2. for every result satisfying that postcondition, establish the specification of the continuation;
3. conclude the specification of the whole bind.

This is the proof-level counterpart of symbolic execution through one monadic call. The tactic finds a specification theorem for the call, instantiates it, creates any theorem preconditions as proof obligations, introduces the returned values and postcondition facts, and leaves the continuation as the next program proof state.

The BaseTutorial checked into the same revision makes this progression explicit: after applying an addition specification, a result variable and equality fact appear in the context and that addition call disappears from the remaining goal.

Basis: **source** + preserved proof example + upstream **documentation**.

### Preconditions are proof obligations, not assumptions silently granted by `step`

A registered specification may require conditions such as integer bounds. `step` first tries to solve such preconditions with configured mechanisms. At this pin the default configuration enables matching local assumptions and `grind`; `scalar_tac` is available but not enabled in the basic step configuration by default. Additional simplification hooks are registered through `step_pre_simps`.

If a precondition cannot be proved, it remains a goal. The proof does not get the callee’s postcondition for free.

This matters when reading compact proofs. A successful `step` line can hide substantial automated arithmetic or logical discharge, but the resulting theorem remains checked by Lean. Failure to discharge a necessary condition does not become a trusted assumption merely because the tactic attempted automation.

Basis: **source** + upstream **documentation**.

### `step as` controls names, while `step with` controls theorem selection

The proof interface separates two frequent sources of brittleness.

`step with foo_spec` explicitly selects a specification theorem rather than asking the database to choose one. `step as ⟨x, h₁, ...⟩` names the returned value and top-level facts introduced from the theorem’s postcondition. Omitting those names may leave inaccessible/generated names in the context.

These forms affect proof ergonomics and script stability. They do not change the proposition being proved.

Basis: upstream **documentation** + checked-in proof examples.

### `step*` is repeated theorem-directed execution plus branch traversal

`step*` repeatedly traverses the current monadic proof state. It applies `step` at calls, simplifies, and explores branches produced by matches and conditionals. Each branch is handled as an independent proof state. The implementation can thread a `grind` state across sequential steps to reuse derived facts, while discarding branch-specific state rather than merging incompatible branch e-graphs.

When it reaches a terminal goal, it attempts to finish with `agrind`. If it cannot, the goal remains unresolved.

Thus `step*` is not an oracle that proves every generated program. It is a composition engine over registered theorems plus ordinary Lean automation.

Basis: **source**.

### `step*?` exposes the automation as an ordinary script

The `step*?` variant runs the same traversal but builds a “Try this” tactic script that spells out selected `step` theorems, branch splits, introduced outputs, and finishing automation. Upstream documentation recommends using this expanded script to understand the proof, repair individual obligations, and then refold it into `step*` once supporting lemmas are available.

The implementation may place `sorry` placeholders into the generated suggestion for unresolved subgoals. Those placeholders describe where the proposed script is incomplete; they are not evidence that the underlying goal was solved. A proof accepted without admissions still requires every resulting Lean goal to close.

Basis: **source** + upstream **documentation**.

### Optional postcondition inference is narrow and disabled by default

The step configuration contains `inferPost`, defaulting to `false`. When enabled, it targets a specific unresolved-goal form: `?post args...`, where the postcondition itself is an unassigned metavariable. `InferPost.lean` synthesizes a predicate from values that escape the local context, assigns the metavariable, and then attempts to prove the resulting goal with `agrind`.

This facility is proof automation for a metavariable already present in the Lean goal. It is not a source-level inference of the programmer’s intended specification, and it should not be treated as an automatically inferred Rust contract.

Basis: **source**.

### Backward functions require no special WP primitive

Aeneas’s mutable-borrow translation can return a value together with a backward function. From the WP library’s perspective this is just a product inside `Result`. The postcondition can destructure the product and specify both the forward result and the backward function.

The upstream proof-strategy documentation uses `choose` as the canonical pattern: a specification receives `z` and `back`, then states which original value `z` corresponds to and how `back z'` reconstructs the owners.

The WP library therefore does not itself encode Rust ownership. The correctness of that functionalization depends on the Aeneas translation semantics and their relation to Rust.

Basis: **source** + upstream **documentation** + **derived** relation to the pinned translation.

### Recursion can make specification reuse itself a termination obligation

Because specification theorems are ordinary Lean theorems, a recursive proof can use its own theorem when `step` reaches a recursive call. The upstream tutorial demonstrates this for a recursive integer function and supplies `termination_by` and `decreasing_by` clauses.

Upstream documentation also warns that a poorly shaped proof can cause `step` to select the theorem currently being proved before a necessary case split, producing a Lean termination error rather than valid circular reasoning.

The important boundary is that recursive specification reuse is not an unchecked assumption. Lean’s theorem termination requirements govern the recursive proof definition.

Basis: **source** + upstream **documentation** + preserved proof example.

### Loop specifications use explicit well-founded reasoning

The tactic reference directs loop proofs to `loop.spec_decr_nat` for a natural-number measure or `loop.spec` for a general well-founded measure. This is separate from merely applying `step` to a sequence of non-looping calls.

The existence of loop helpers does not imply automatic total-correctness proofs for arbitrary translated loops. A proof still needs the invariant, postcondition, and required decreasing relation.

Basis: upstream **documentation**.

### Historical Anneal V1 split upstream `spec` into progress and correctness goals

Anneal V1 defined:

`wp_prove_orthogonal : (∃ y, m = .ok y) → (∀ y, m = .ok y → P y) → WP.spec m P`.

This is a direct decomposition of the upstream fact that `spec m P` means an `ok` result satisfying `P`. V1 then introduced `eval_progress` and a proof UI that treated existence of a successful result separately from the returned-value correctness proof.

The split is useful historical evidence about one way to consume Aeneas’s WP interface. It is not part of Aeneas itself. Current Anneal V2 principles require precise success semantics and fail-closed behavior but deliberately leave the proof encoding undecided.

Basis: historical Anneal **source** + **derived** relation to upstream Aeneas source.

## Boundaries

- No fresh Lean elaboration, tactic execution, Aeneas translation, or Charon extraction was performed.
- Checked-in `.lean` files and tutorial examples are preserved source/proof artifacts. This report does not claim to have rerun them on this surface.
- `WP.spec` gives total successful-return semantics for the translated `Result` computation. It does not by itself prove that the translated computation faithfully models every relevant Rust behavior.
- The basic `spec` predicate treats both `fail` and `div` as failure to satisfy the specification. It does not preserve their distinction in the final successful-spec proposition.
- This report describes the ordinary functional Aeneas Lean backend. It does not establish the semantics of current separation-logic work or future unsafe-Rust backends.
- Aeneas does not provide a per-translated-function generated WP theorem in the examined extraction path. Narrow Lean metaprogramming helpers do generate some `step` theorems for pure definitions.
- `step` correctness depends on the correctness of the specification theorem it applies and on Lean checking the generated proof term. Tactic success is not independent evidence that an upstream model theorem is semantically adequate for Rust.
- `step*` is automation, not a completeness theorem. Unsupported program shapes, missing specifications, unresolved theorem arguments, unresolved preconditions, or hard terminal goals can stop it.
- `inferPost` does not infer developer intent; it assigns a Lean metavariable in a narrow proof state.
- Loop and recursive proof support was inspected only far enough to establish the proof-interface shape. This report does not inventory every partial-function or termination facility.
- Historical V1 “Orthogonal WP” is not current Anneal design authority.

## Evidence

**Source — primary Aeneas revision.** `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`.

- `backends/lean/Aeneas/Std/Primitives.lean`, blob `bb730a91a4172fa5bd162f13c3e50bb8e9282b1f`: `Result`, `bind`, Monad support, partial-fixpoint support.
- `backends/lean/Aeneas/Std/WP.lean`, blob `018c456bcab5374de0b09b17eda0df1a48e2288b`: `Wp`, `theta`, `spec`, `spec_bind`, `spec_bind'`, `spec_mono`, `spec_mono'`, `spec_equiv_exists`, Hoare notation.
- `backends/lean/Aeneas/Tactic/Step/Init.lean`, blob `afaa4f2243a4d6bfcf08b36eff282886ed175ef2`: step configuration, simp attributes, `@[step]` theorem database, threaded state.
- `backends/lean/Aeneas/Tactic/Step/Step.lean`, blob `7939a977951e96143cda58b27094db0274c89ed2`: theorem matching, bind/mono composition, precondition discharge, output introduction, tactic syntax.
- `backends/lean/Aeneas/Tactic/Step/StepStar.lean`, blob `710371a5675e053ce59c0d961ab5465ff0633738`: repeated traversal, branch handling, finishing automation, script generation.
- `backends/lean/Aeneas/Tactic/Step/InferPost.lean`, blob `1de2fa4219832273f750b82abf3118c006aeeab6`: optional postcondition metavariable inference.
- `src/extract/Extract.ml`, blob `52754e4fdb25b50fce63abe2d2184751d69632e8`: extraction of translated function declarations and Lean termination/decreasing clauses.

**Documentation — same Aeneas revision.**

- `documentation/tactics-reference.md`, blob `d09ac06bc02835e354a9fe7e6829762962439f2a`.
- `documentation/proof-strategies.md`, blob `2b10ed04a1594d6b8a95a80c742af10885974143`.

**Preserved proof examples — same Aeneas revision.**

- `tests/lean/BaseTutorial.lean`, blob `52a9947feab2f607729e23c10dfc9e12bba02d41`: manual `step`, registered specs, recursive specification proof.
- `tests/lean/Demo/Properties.lean`, blob `fc3182dd7ce98fa9052a680b863ab7100feb1f4c`: `step`, `step*`, recursion, backward-function postconditions.

**Toolchain identity — same Aeneas revision.**

- `backends/lean/lean-toolchain`, blob `6c7e31fffe3e03be3e0d7021acd9cd848e44db26`: `leanprover/lean4:v4.30.0-rc2`.
- `backends/lean/lake-manifest.json`, blob `1a5af703163d8b39f4311aafe22ae171788179ee`: Mathlib revision `5450b53e5ddc75d46418fabb605edbf36bd0beb6`.

**Historical Anneal V1 source.** `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`.

- `anneal/v1/src/Anneal.lean`, blob `727199a54622d56dd429f2b3b178748f2cc5b7f1`: `SpecificationHolds`, `wp_prove_orthogonal`, `eval_progress`.
- `anneal/v1/docs/agent/05_proof_architecture.md`, blob `8f7f589c629876a4696ed86f215ba1c050a4ba36`: historical Orthogonal WP explanation.
- `anneal/v1/docs/agent/06_tactics_and_tooling.md`, blob `c8aac2f6cfdb244bafce5bc90669a679e6ab65fd`: historical progress-tactic interface and use of `spec_imp_exists`.

No evidence gathered by this report is fresh **execution**.

## Revalidation

For a later Aeneas pin, the cheapest source-level discriminator is:

1. inspect `Std/Primitives.lean` for the `Result` constructors and `bind`;
2. inspect `Std/WP.lean` for `theta`, `spec`, `spec_equiv_exists`, `spec_bind'`, and the `⦃ ... ⦄` elaboration;
3. inspect `Tactic/Step/Init.lean` for the `@[step]` registry and default tactic configuration;
4. inspect `Tactic/Step/Step.lean` and `StepStar.lean` for theorem lookup, precondition discharge, bind composition, branch traversal, and unresolved-goal behavior;
5. inspect `InferPost.lean` before relying on inferred postconditions;
6. compare the checked-in BaseTutorial and Demo specifications, especially one arithmetic bind, one recursive call, and one mutable-borrow backward function.

On a capable execution surface, use the exact pinned Lean toolchain and create one small Lean file importing `Aeneas`. Define a two-bind `Result U32` function and a `@[step]` specification for the first call. Check four variants: a satisfiable precondition, an unsatisfied precondition, a missing `@[step]` theorem, and a conditional branch. Run the proof once with explicit `step`, once with `step*`, and once with `step*?`; preserve the resulting goals or generated script. Add a function returning a pair `(value, back)` and confirm the same notation/spec machinery destructures both values. Finally prove directly that `spec (fail e) P` and `spec div P` cannot be closed without contradiction.

That experiment revalidates the proof-facing behavior of the exact toolchain. It does not establish the semantic adequacy of the Rust-to-Aeneas translation or prove that every translated Rust construct has an applicable specification theorem.
