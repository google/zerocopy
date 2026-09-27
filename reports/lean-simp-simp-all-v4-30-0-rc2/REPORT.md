# Lean `simp` and `simp_all` behavior at v4.30.0-rc2

## Summary

At `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (`v4.30.0-rc2`), `simp` and `simp_all` share the same simplifier engine but expose materially different context behavior.

`simp` simplifies the selected target and/or hypotheses using the default `[simp]` theorem and simproc sets plus explicit arguments. Its default configuration is non-contextual. `simp_all` instead uses `Simp.ConfigCtx`, whose default enables contextual simplification, adds every local proposition as a simp theorem, repeatedly simplifies the nondependent proposition hypotheses and target until no further change occurs, and then rebuilds the changed context. Dependent proposition hypotheses can contribute rewrite facts to `simp_all`, but they are not themselves among the hypotheses that `simp_all` rewrites and reasserts.

For generated proof scripts, `simp only [...]` is the strongest built-in way in this interface to reduce dependence on the imported default simp set: it discards the ordinary default simp theorem set and default simprocs, retaining only `eq_self`, `iff_self`, and explicitly supplied entries. It does not disable the simplifier's built-in reductions, congruence traversal, or other configuration-controlled behavior, so it is narrower than plain `simp` but is not a literal rewrite-only interpreter.

Both tactics fail by default when they make no progress. Plain `simp` also supports a custom discharger and location syntax; `simp_all` does not support either through this tactic interface. `simp!` and `simp_all!` are macros that set `autoUnfold := true`, expanding the simplification surface to pattern-matching function applications.

No fresh Lean execution was performed. The findings below come from exact pinned Lean source.

## Applicability

This report applies to Lean 4 revision `3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`, released as `v4.30.0-rc2`, and specifically to the built-in `simp`, `simp!`, `simp_all`, and `simp_all!` tactic implementations and their underlying simplifier at that revision.

The report focuses on behavior that affects generated or mechanically maintained proof scripts: which facts enter the simplifier, how local context changes the result, what `only`, `*`, locations, and `!` mean, how rules are selected and repeated, when goals close or tactics fail, and which defaults create implicit dependencies.

It does not claim source compatibility or behavioral stability across Lean revisions. The implementation has no compatibility layer that freezes these tactic internals independently of the Lean version, so a generated-proof consumer should bind these conclusions to this exact pin and revalidate on upgrade.

## Findings

### Plain `simp` starts from the imported default simp environment unless `only` is used

`mkSimpContext` obtains the default theorem set from `getSimpTheorems`, the environment extension populated by `[simp]`, and obtains the default simproc set from `Simp.getSimprocs`. Explicit tactic arguments are then added to that context.

With `simp only`, the default theorem set is replaced by a fresh set containing only `eq_self` and `iff_self`, and the default simproc set is empty before explicit arguments are processed. Therefore imported additions to `[simp]` or to the default simproc registry cannot directly add rewrite procedures to a `simp only [...]` call.

This is an important but bounded stability property. `simp only` still uses the normal simplifier engine and its configuration. At the default configuration that includes beta, iota, projection, zeta, unused-let simplification, congruence traversal, definitional-equality checks, and repeated simplification. `only` narrows the theorem/simproc inputs; it does not turn those other mechanisms off.

Basis: **source**.

### Explicit simp arguments can add rules, unfold definitions, reverse rules, erase rules, or add local facts

The tactic argument elaborator distinguishes several effects:

- a proposition theorem or proof becomes one or more simp rewrite entries;
- a named definition becomes unfolding/equation entries;
- `←` reverses an equality or iff rule when that reversal is valid;
- `- name` erases a rule or simproc from the active context;
- a registered custom simp/simproc extension can be added as a separate set;
- `*` in a plain `simp` argument list adds the current local proposition hypotheses as simp theorems.

Proposition facts are normalized into rewrite form before entering the simp set. Equality and iff facts become equality rewrites, ordinary proposition facts become rewrites to `True`, negations become rewrites to `False`, and conjunctions can contribute multiple rules. This is why adding a local proposition hypothesis can materially change simplification even when it is not syntactically an equality.

For a definition named in a simp argument, Lean prefers generated equation theorems when available and may also register the declaration for unfolding. Equation entries receive priorities intended to try more specific equations before catch-all equations.

Basis: **source**.

### `simp [*]`, `simp at *`, and `simp_all` have different local-context semantics

These three forms should not be treated as interchangeable.

`simp [*]` uses `*` as a simp-set argument. It adds all proposition hypotheses as rewrite theorems, then simplifies the location selected by the tactic.

`simp at *` uses `*` as a location. The location handler selects all nondependent proposition hypotheses plus the target for simplification. It does not, merely by choosing that location, add all of those hypotheses to the simp theorem set. Each selected hypothesis is simplified with itself temporarily erased from the active theorem set.

`simp_all` does both more context ingestion and more iteration. At initialization it adds every local proposition hypothesis to the simp theorem set unless explicitly erased. It creates mutable simplification entries only for the nondependent proposition hypotheses. It then repeatedly simplifies those entries and the target until a pass makes no change or closes the goal.

Thus a dependent proposition hypothesis can influence `simp_all` as a rewrite fact even though `simp_all` does not rewrite and reassert that hypothesis itself.

Basis: **source**.

### `simp_all` is a fixed-point context transformation, not a single `simp` call over many locations

`SimpAll.loop` simplifies each tracked nondependent proposition hypothesis while temporarily removing that hypothesis's own rule, then simplifies the target. When a hypothesis changes, Lean removes the old local theorem and adds the simplified version under a fresh origin so later hypotheses and the target can use the new fact. If anything changed, the loop starts another round.

The self-removal is intentional. Without it, a hypothesis could simplify itself to `True`; similarly, identical hypotheses could erase useful information by simplifying each other to `True`. After the fixed point, hypotheses reduced to `True` are dropped. Lean reasserts changed hypotheses beginning at the first changed entry so that it preserves original hypothesis order as far as this transformation permits.

This makes `simp_all` substantially more sensitive than plain `simp` to the complete local proposition context. Adding a proposition that never appears as an explicit tactic argument can still alter which rules fire, which hypotheses survive, and whether the target closes.

Basis: **source**.

### `simp_all` is contextual by default; plain `simp` is not

`Simp.Config` defaults `contextual := false`. `Simp.ConfigCtx`, used specifically for `simp_all`, extends that configuration with `contextual := true`.

When contextual simplification descends under an implication `p → q`, Lean can add the local proof of `p` to the active simp theorem set while simplifying `q`. The implementation resets the relevant cache when local facts are introduced so that cached results from a smaller context are not reused unsafely.

The local-context sensitivity of `simp_all` therefore has two sources at this revision: it globally seeds the simp set from local proposition hypotheses, and its default simplifier configuration also admits newly introduced proposition assumptions while traversing propositions.

Basis: **source**.

### Rule application is indexed and priority-ordered, with explicit loop controls

The default configuration uses indexed simp-theorem lookup. For a candidate expression, Lean retrieves matching theorems from discrimination trees and sorts them by descending priority before trying them. The first applicable candidate in that ordered traversal wins for that rewrite opportunity. Setting `index := false` switches to a more liberal root-symbol lookup intended to approximate Lean 3 behavior.

The simplifier also protects against several nontermination modes. A theorem whose result is structurally equal to the input after metavariable instantiation is rejected. A permutation theorem, where left- and right-hand sides are identical modulo variable permutation, is applied only when the right-hand side decreases according to Lean's `acLt` order. The simplifier counts steps and, with the default `maxSteps := 100000`, raises an error if the step bound is exceeded.

At the expression level, `singlePass := false` by default. After pre-processing, recursive/congruence simplification, and post-processing, the engine re-enters the simplification loop when the expression changed. This repeated expression-level behavior is separate from the outer fixed-point loop that `simp_all` performs over the hypotheses and goal.

Basis: **source**.

### Conditional rules can recursively discharge side conditions

When a simp rule leaves propositional metavariables to solve, Lean can try typeclass synthesis and then a discharger. The default discharger first has special handling for equation-theorem hypotheses, then recursively invokes the simplifier on the side condition. It accepts the side condition when simplification yields `True` or a supported reflexive proof.

`maxDischargeDepth` defaults to `2`, and `discharge?'` rejects deeper recursive discharge attempts. Unsuccessful discharges restore the accumulated used-theorem state so failed attempts do not look like successful simp uses.

Plain `simp` also accepts a custom tactic discharger. The tactic wrapper runs that discharger with `try`, requires a complete proof with no remaining metavariables, and preserves only the relevant term-elaboration messages and info-tree effects. `simp_all` rejects the custom discharger option in `mkSimpContext`, even though its generated parser shape shares the general simp-like syntax machinery.

Basis: **source**.

### The default configuration contains several implicit proof-script dependencies

At this revision the most relevant `Simp.Config` defaults are:

- `maxSteps := 100000`;
- `maxDischargeDepth := 2`;
- `contextual := false` for plain `simp`, overridden to `true` by `ConfigCtx` for `simp_all`;
- `memoize := true`;
- `singlePass := false`;
- `zeta := true`, `beta := true`, `iota := true`, and `proj := true`;
- `decide := false`, `arith := false`, and `autoUnfold := false`;
- `dsimp := true` for dependent arguments when no suitable congruence theorem permits ordinary simp traversal;
- `failIfUnchanged := true`;
- `unfoldPartialApp := false` and `zetaDelta := false`;
- `index := true`;
- `implicitDefEqProofs := true`;
- `zetaUnused := true`, `catchRuntime := true`, and `zetaHave := true`;
- `locals := false` and `instances := false`.

`eta := true` is present in the configuration, but its own source documentation says the function-eta reduction option is currently unimplemented. Generated proof logic should not infer an implemented eta pass merely from that field's default value.

Basis: **source**.

### `simp!` and `simp_all!` widen unfolding by enabling `autoUnfold`

The built-in macro declarations define `simp!` as `simp` with `autoUnfold := true` and `simp_all!` as `simp_all` with the same setting. `autoUnfold` permits the simplifier to unfold applications of pattern-matching definitions when one of their patterns applies.

That behavior is materially broader than ordinary `simp`, whose default has `autoUnfold := false`. A generator that chooses `simp!` is therefore opting into a larger and more definition-sensitive simplification surface than one that emits otherwise identical `simp` syntax.

Basis: **source**.

### Both tactics treat no progress as failure by default

`failIfUnchanged := true` is the default. `simpGoal` raises `` `simp` made no progress `` if the resulting goal metavariable is unchanged, and `simpAll` raises `simp_all made no progress` when its result is the same goal metavariable.

This matters for generated scripts that are replayed after surrounding proof obligations change. A `simp` step that was useful when generated can become a tactic failure if earlier elaboration or proof changes make the goal already simplified. Conversely, setting `failIfUnchanged := false` changes that control-flow contract and permits the tactic to succeed as a no-op.

Basis: **source**.

### Simplification can close the goal through either the target or a hypothesis

When target simplification produces `True`, `simpTargetCore` assigns a proof and closes the goal. When simplification of a selected hypothesis produces `False`, the simplifier derives the goal by false elimination and closes it.

`simp_all` inherits both behaviors while iterating over its tracked hypotheses and target. Therefore a generated script must not assume that a successful simplifier invocation always returns a residual goal for a following tactic.

Basis: **source**.

### `simp only` is the best built-in dependency-narrowing form, but not a complete isolation boundary

For generated proofs that should avoid accidental dependence on imported `[simp]` growth, `simp only [named entries...]` removes the two largest ambient extension inputs: the default theorem extension and default simproc extension. This is a **derived** consequence of `mkSimpContext`.

It does not freeze all simplification semantics. Built-in reductions and congruence behavior still depend on the pinned Lean implementation and configuration; explicit definitions can expand through their equation theorems; conditional rules invoke discharge machinery; and proposition arguments can be preprocessed into several rewrite entries. Consequently `simp only` should be read as explicit simp-set control, not as a cross-version semantic sandbox.

Basis: **derived** from pinned **source**.

### `simp_all` should be treated as consuming the whole proposition context

For a generated proof, the effective input to `simp_all` includes more than its explicit argument list. Every local proposition can enter the simp set, simplified nondependent propositions are fed back as new rules, and contextual simplification can introduce proposition assumptions while descending under implications.

Therefore a generator that uses `simp_all` should treat changes to the local proposition context as possible proof-script changes even when the tactic text itself is unchanged. This is not an implementation accident: it is the central algorithm implemented by `SimpAll` and `ConfigCtx` at this revision.

Basis: **derived** from pinned **source**.

## Boundaries

No fresh Lean executable, Lake environment, generated Anneal proof, or Aeneas-produced theorem was executed. The report establishes the pinned source semantics and control flow, not empirical success rates on Anneal output.

The report does not characterize the `linter.unusedSimpArgs` warning algorithm. `evalSimp` and `evalSimpAll` invoke that linter after successful simplification when its options permit, but detailed linter behavior is a separate reference subject.

The report does not characterize `simp?` or `simp_all?` suggestion quality, library suggestion engines, trace rendering, or the exact text of suggested replacement scripts.

The source establishes how the active simp set is built and how candidate rules are tried. It does not establish a stable tie-breaking contract for two distinct applicable rules with equal priority beyond the concrete implementation at this revision; generated scripts should not rely on an undocumented equal-priority ordering guarantee.

The report does not claim that `simp only` is independent of imported declarations. Explicitly named theorems and definitions, their types/bodies/equation theorems, congruence declarations, and the Lean kernel/elaborator environment remain part of the proof's meaning.

The report does not claim that contextual simplification makes arbitrary dependent hypotheses rewriteable. `simp_all` adds all proposition hypotheses as rewrite theorems, but only nondependent proposition hypotheses are tracked as entries to simplify and reassert.

## Evidence

**Subject.** `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (`v4.30.0-rc2`). Evidence was acquired on 2026-09-27.

Primary pinned **source**:

- `src/Lean/Elab/Tactic/Simp.lean`, blob `3e6308c7cf806f921484155e8ff8295804b0ef45`: simp-argument elaboration, `only`, `*`, context construction, locations, custom dischargers, and `evalSimp`/`evalSimpAll`.
- `src/Lean/Meta/Tactic/Simp/SimpAll.lean`, blob `7cb9d3e7fc4618537374ff683593639a106d3175`: `simp_all` context initialization, nondependent-hypothesis tracking, repeated fixed-point loop, rule replacement, context reconstruction, and fail-if-unchanged behavior.
- `src/Lean/Meta/Tactic/Simp/Main.lean`, blob `f8c2607a24cd93490265cd18cd5ea0c73539d628`: simplifier loop, reductions, contextual local facts, goal/hypothesis application, step bound, target closure, and `simpGoal` behavior.
- `src/Lean/Meta/Tactic/Simp/Rewrite.lean`, blob `1ca46b5bb347aacc3c0e04b32bb17a678d0883d7`: theorem lookup and priority ordering, side-condition synthesis/discharge, permutation-rule ordering, and default discharge implementation.
- `src/Lean/Meta/Tactic/Simp/SimpTheorems.lean`, blob `4945b5ad5a4962e4be4b25ce2fbc43316cf47a30`: theorem representation, preprocessing of propositions into rewrite rules, reverse-rule handling, permutation detection, theorem priorities, and definition equation entries.
- `src/Lean/Meta/Tactic/Simp/Attr.lean`, blob `6f32b30f1af3a65538125fe5b8fbe2785e7c86c0`: `[simp]` and custom simp-set environment extensions plus definition registration.
- `src/Init/MetaTypes.lean`, blob `5ad9df892066c95c13883c0041a8a36ac30dfcda`: exact `Simp.Config` defaults and the `Simp.ConfigCtx` override used by `simp_all`.
- `src/Init/Meta.lean`, blob `5c65176d064ead7a2b58d07624fcbdd159a805c2`: generated simp-like tactic syntax and the `simp!`/`simp_all!` `autoUnfold := true` macros.

There is no fresh **execution** evidence in this package. Recommendations about generated-proof dependency surfaces are explicitly **derived** from these source behaviors.

## Revalidation

For another Lean revision, the cheapest reliable revalidation is source-first:

1. diff `src/Init/MetaTypes.lean` for `Simp.Config` and `ConfigCtx` defaults;
2. diff `src/Lean/Elab/Tactic/Simp.lean` for `mkSimpContext`, `elabSimpArgs`, `applyStarArg`, `simpLocation`, `evalSimp`, and `evalSimpAll`;
3. diff `src/Lean/Meta/Tactic/Simp/SimpAll.lean` for `initEntries`, `loop`, `main`, and `simpAll`;
4. diff `src/Lean/Meta/Tactic/Simp/Main.lean`, `Rewrite.lean`, and `SimpTheorems.lean` for the core loop, candidate selection, discharge, rule preprocessing, and termination guards;
5. diff the simp-like tactic declarations in `src/Init/Meta.lean` for `simp!` and `simp_all!`.

If those regions changed materially, run a small pinned probe before carrying the conclusions forward. The probe should distinguish at least: plain `simp` versus `simp only`; `simp [*]` versus `simp at *`; `simp_all` with a dependent proposition and a nondependent proposition; contextual simplification under an implication; a conditional simp rule that needs discharge; a no-op with default and disabled `failIfUnchanged`; and `simp` versus `simp!` on a pattern-matching definition. Preserve the exact Lean revision, source input, command, and output.

A passing probe covers only those cases. It does not by itself re-establish the complete rule-selection and context-transition model described above.