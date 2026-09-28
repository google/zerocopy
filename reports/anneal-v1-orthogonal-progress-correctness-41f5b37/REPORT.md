# Anneal V1 orthogonal progress/correctness architecture at `41f5b37`

## Summary

Retained Anneal V1 deliberately splits a function specification into two independent Lean obligations:

1. **progress:** the translated Aeneas computation has some successful result, `∃ y, m = .ok y`;
2. **correctness:** every successful result satisfies the postcondition, `∀ y, m = .ok y → P y`.

The split is implemented by `Anneal.wp_prove_orthogonal` and generated for proof-mode function specifications before Anneal instantiates the per-field `Post` structure. Its purpose is diagnostic: a stuck weakest-precondition evaluation should not prevent Lean from type-checking and independently reporting the correctness fields that would hold *conditional on successful evaluation*.

That conditionality is also the central vacuity observation. The correctness branch by itself says nothing about a computation that returns `fail` or `div`, because there is no equality `m = .ok y` to assume. It is intentionally vacuous in those cases. The final theorem is not weakened when both branches are proved: the progress branch rules out `fail` and `div`, while the correctness branch proves `P` for the resulting value. This matches the pinned Aeneas `WP.spec`, which is false on `fail` and `div` and reduces to `P x` on `.ok x`.

The split has an engineering cost. Proof facts do not flow from the progress branch into the correctness branch. `proof context:` runs only after the split, where `h_returns` is an equality rather than a live `WP.spec`; the historical documentation therefore says Aeneas `progress` cannot be used there. In addition, omitted correctness fields run independent `autoParam` tactics that each unfold/split `h_returns`, repeating normalization work to preserve independent diagnostics. Shared ordinary logical setup can be factored through `proof context:`, but progress-oriented setup cannot.

No fresh historical toolchain execution was performed. The observations below come from the retained implementation, the exact Aeneas revision it pins, and V1's checked-in design record. A small retained-toolchain probe remains useful for preserving concrete diagnostic and performance behavior.

## Applicability

This report applies to:

- `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`, retained `anneal/v1`;
- Aeneas revision `42c0e90dacf486f7d3ed5b6cde3a9a81f04915a4`, pinned by that V1 `Cargo.toml`;
- Lean `v4.30.0-rc2`, also pinned by retained V1.

It addresses the #3720 item:

> **V1 orthogonal progress/correctness experiment** — proof duplication and vacuity observations.

The separate completed **V1 `unsafe(axiom)` semantics** item remains authoritative for axiom-mode behavior, including whether an axiom asserts progress. This report concerns the generated theorem/proof path.

## Findings

### Aeneas `WP.spec` already rejects failure and divergence

At the exact Aeneas revision consumed by V1, `Result α` has three constructors: `ok`, `fail`, and `div`. `WP.spec m P` is defined by `theta m P`:

- for `ok x`, it reduces to `P x`;
- for `fail _`, it reduces to `False`;
- for `div`, it reduces to `False`.

So the target theorem is not merely partial correctness of successful executions. A proof of `WP.spec m P` must also exclude Aeneas-level failure and divergence.

Basis: **source** — pinned Aeneas `Primitives.lean` and `WP.lean`.

### `wp_prove_orthogonal` decomposes one strong specification into progress plus conditional correctness

Anneal defines:

```lean
theorem wp_prove_orthogonal {α} {m : Result α} {P : α → Prop} :
  (∃ y, m = .ok y) →
  (∀ y, m = .ok y → P y) →
  WP.spec m P
```

The proof is direct: the first premise supplies a successful result `y` and equality `hy`; rewriting `m` with `hy` reduces the target to the postcondition, which the second premise supplies.

Generated theorem proofs immediately `apply Anneal.wp_prove_orthogonal`. Anneal then emits the progress subgoal first and the correctness subgoal second.

This is a proof-organization change, not a semantic relaxation, **provided both premises are proved without admissions**.

Basis: **source** — `anneal/v1/src/Anneal.lean` and `generate.rs`.

### The correctness branch is vacuous on `fail` and `div` when viewed in isolation

The correctness premise has the shape:

```text
∀ y, m = .ok y → P y
```

For `m = fail e` or `m = div`, there is no `y` for which `m = .ok y`. The implication is therefore trivially true for every `y`.

This is not a bug in the combined theorem. It is the intended conditional half of the decomposition. The progress premise supplies the non-vacuity condition by proving that an `ok` result exists. Together, the premises recover the strength needed by `WP.spec`.

The important interpretation rule is therefore:

> A correctness-field proof in V1 is a proof **conditional on successful progress**. It is not, by itself, evidence that the translated computation cannot fail or diverge.

The checked-in V1 agent documentation states the same point explicitly: correctness is “actually a proof of correctness conditional on progress,” represented by `h_returns`.

Basis: **source** + retained **documentation**.

### The split was designed to preserve correctness diagnostics when progress is stuck

Before the split, a stuck WP prevented Lean from reaching the granular postcondition structure. The Named Bounds design records this as the motivating failure: an opaque or otherwise non-evaluable execution step could stop the entire function proof and hide whether individual `ensures` and injected validity bounds were otherwise provable.

After the split, Anneal builds two sibling goals. The correctness branch introduces an arbitrary successful result and `h_returns : m = .ok y`, then constructs the `Post` record. Each field can therefore elaborate and fail independently even if the separate progress branch cannot be solved automatically.

This is what “orthogonal” means operationally in retained V1: **diagnostic independence**, not logical independence of the final theorem. The final theorem still needs both branches.

Basis: **source** + `docs/design/named_bounds.md`.

### Facts proved during progress are not shared with correctness

Sibling Lean goals do not share tactic-local facts. A user can provide a custom `proof (h_progress):` block, but hypotheses or intermediate values created there do not become assumptions in the correctness branch.

The correctness branch receives:

- the original theorem arguments and preconditions;
- an abstract successful result;
- `h_returns`, equating the Aeneas computation with that `.ok` result.

This separation is what makes correctness independently elaboratable, but it also means operational reasoning performed solely to establish progress may need to be reconstructed from `h_returns` or repeated when proving postconditions.

Basis: **source-derived** from generated sibling goals.

### `proof context:` cannot be the shared home for WP progress reasoning

The historical Named Bounds document records a specific limitation: `proof context:` executes inside the correctness branch, after `wp_prove_orthogonal` has split the WP. At that point the relevant object is `h_returns`, an equality such as `test_func = ok ret_`, not a `WP.spec` goal.

Aeneas's `progress` tactic is designed to step weakest-precondition expressions. It therefore cannot be used in this post-split proof context. V1's documentation tells users to move such reasoning to `proof (h_progress):` or to the specific correctness field that needs it.

This limits how much duplicated operational setup can be factored into a single shared context.

Basis: retained **documentation**, consistent with generated **source** shape.

### Independent correctness fields deliberately repeat some normalization work

Anneal's Named Bounds design optimizes for independent field evaluation. If a user omits an explicit proof for a postcondition or injected validity bound, Lean uses that field's `autoParam` tactic.

The retained macros `verify_user_bound` and `verify_is_valid` each independently operate on `h_returns`; both begin by attempting to unfold the translated function at that hypothesis and split it before trying their own automation chain. If several omitted fields need the same normalization, those steps are repeated per field.

This is an explicit tradeoff:

- **benefit:** one field's failure does not prevent other fields from elaborating and producing targeted diagnostics;
- **cost:** common normalization and automation can be repeated, and tactic-local results are not automatically shared among fields.

A `proof context:` can factor pure term-mode facts that are valid for all fields, but it cannot run the WP-oriented `progress` tactic after the orthogonal split.

This is the strongest source-visible “proof duplication” effect. It is a structural consequence of independent field evaluation; this report does not claim a measured runtime cost without a fresh retained-toolchain benchmark.

Basis: **source** — `Anneal.lean` autoParam macros and generated `exact { ... }` structure; **derived** cost.

### `--allow-sorry` makes the progress branch a visible trust boundary

`eval_progress` first attempts to unfold/split and construct an `ok` witness. If that fails, it calls `eval_allow_sorry_or_fail`. Under ordinary mode, this produces a hard error. When Anneal's `--allow-sorry` support has installed its admission marker, the fallback uses `sorry`.

Because correctness is conditional on `m = .ok y`, admitting progress is materially different from proving it: the admission supplies exactly the premise that rules out `fail` and `div`. A correctness branch can still elaborate and even be vacuously true for those bad outcomes, while the admitted progress premise lets the combined theorem close.

That behavior is consistent with the flag's purpose as a prototyping escape hatch. It means results produced with `--allow-sorry` must not be read as completed progress proofs.

Basis: **source** — `Anneal.lean`; **derived** from the orthogonal theorem.

### The generated theorem uses Aeneas `WP.spec`, not the similarly shaped helper `SpecificationHolds`

Retained `Anneal.lean` also defines `Anneal.SpecificationHolds`, which directly pattern-matches on `Result`: `ok` checks the postcondition and `fail`/`div` are false. That helper has the same important success/failure/divergence boundary.

However, the generator's actual function-spec theorem target is `Aeneas.Std.WP.spec`. The report therefore grounds the semantic claim in the exact pinned Aeneas definition rather than treating `SpecificationHolds` as the generated ABI.

Basis: **source** — `generate.rs`, `Anneal.lean`, pinned Aeneas `WP.lean`.

## What the historical experiment establishes

The retained implementation and its design record support four durable observations:

1. **No semantic weakening when complete.** Proving progress and conditional correctness is sufficient for the original Aeneas `WP.spec` target.
2. **Conditional correctness is vacuous alone.** A field proof says nothing about fail/div unless the sibling progress obligation is also discharged.
3. **Diagnostics improve by separating failure domains.** A stuck progress proof no longer structurally prevents correctness fields from elaborating and reporting their own failures.
4. **The separation can duplicate reasoning.** Progress-local facts are unavailable to correctness; per-field automation independently normalizes `h_returns`; and WP progress tactics cannot be shared through correctness-side `proof context:`.

These are architectural observations. The checked-in corpus does not preserve a controlled timing/diagnostic transcript quantifying the duplication cost, so that empirical part remains re-runnable rather than claimed here.

## Boundaries

- No fresh Lean, Aeneas, or Anneal V1 execution was performed.
- “Proof duplication” here means source-visible repeated proof/normalization structure and branch-local reasoning, not a measured performance regression.
- This report does not claim that every correctness proof actually repeats work; explicit proofs and `proof context:` can factor many ordinary facts.
- This report does not claim the correctness branch is unsound because it is vacuous on bad outcomes. The final theorem remains strong when progress is genuinely proved.
- `--allow-sorry` is intentionally an admission mode. The report records how orthogonality localizes that admission; it does not treat admitted proofs as verified results.
- `unsafe(axiom)` is out of scope because V1 emits an axiom rather than following the ordinary generated-theorem proof path; its progress/correctness semantics have a separate #3720 item.
- Aeneas translation correctness, the Rust→Aeneas semantic correspondence, and current Anneal V2 proof architecture are separate questions.

## Evidence

**Retained Anneal V1 source — `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`.**

- `anneal/v1/src/Anneal.lean` — `wp_prove_orthogonal`, `eval_progress`, and per-field `verify_is_valid` / `verify_user_bound` automation.
- `anneal/v1/src/generate.rs` — generated `WP.spec` target, application of the orthogonal lemma, explicit/automatic progress branch, `h_returns` correctness branch, proof context, and `Post` field instantiation.
- `anneal/v1/Cargo.toml` — pins Aeneas `42c0e90dacf486f7d3ed5b6cde3a9a81f04915a4` and Lean `v4.30.0-rc2`.

**Retained V1 design record.**

- `anneal/v1/docs/design/named_bounds.md` — identifies orthogonality as a design criterion, records the pre-split “stuck WP hides correctness diagnostics” problem, describes the generated two-goal architecture, and records the inability to use `progress` inside post-split `proof context:`.

**Pinned Aeneas semantics.**

At `AeneasVerif/aeneas@42c0e90dacf486f7d3ed5b6cde3a9a81f04915a4`:

- `backends/lean/Aeneas/Std/Primitives.lean` defines `Result.ok`, `Result.fail`, and `Result.div`;
- `backends/lean/Aeneas/Std/WP.lean` defines `WP.spec` via `theta`, with `spec_ok ↔ P x`, `spec_fail ↔ False`, and `spec_div ↔ False`.

## Revalidation

A compact exact-toolchain experiment should preserve the historical behavior with five cases.

**Case A — progress succeeds, correctness fails.** Use a trivially evaluable function with a deliberately false `ensures`. Confirm the progress branch closes while the named correctness field reports the failure.

**Case B — progress stalls, correctness is trivial.** Use a function whose Aeneas computation reaches an opaque/unsupported step but whose conditional postcondition is trivial. Confirm that correctness fields still elaborate and that the primary unsolved obligation is progress.

**Case C — admitted progress.** Repeat Case B with `--allow-sorry`. Confirm that the progress admission permits the combined theorem to close while correctness remains merely conditional. Record the emitted warning/assumption evidence.

**Case D — repeated field normalization.** Give one function two or more omitted postcondition fields that all need `h_returns` normalization. Capture Lean traces or tactic diagnostics showing each `autoParam` invocation independently unfolds/splits the same result equality. Compare with a version that factors reusable non-progress facts into `proof context:`.

**Case E — proof-context boundary.** Attempt Aeneas `progress` inside `proof context:` and preserve the failure. Move the same operational reasoning into `proof (h_progress):` and record the successful shape.

For each case, retain the Rust annotation, generated Lean, Lean JSON diagnostics, exact command/flags, and toolchain identities. That would upgrade the source-derived duplication observations into a directly measured historical experiment without changing the logical conclusions above.
