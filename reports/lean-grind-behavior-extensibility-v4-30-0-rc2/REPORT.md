# Lean `grind` behavior and extensibility at v4.30.0-rc2

## Summary

At `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (`v4.30.0-rc2`), `grind` is a bounded proof-search engine built around normalization, congruence closure, theorem instantiation, branching, and registered theory solvers. Its terminal search repeatedly gives registered solvers first opportunity to make progress, then tries E-matching instantiation, case splitting, and model-based theory combination. The search uses continuation-passing actions so branching steps can perform non-chronological backtracking and so tracing can recover replayable tactic scripts that retain only proof-relevant search steps.

The default search is deliberately broad. Its configuration enables E-matching, case splitting, extensionality, function extensionality, model-based theory combination, ring reasoning, linear arithmetic, integer/natural linear arithmetic, associative/commutative reasoning, injectivity, order reasoning, and function-valued congruence closure. The defaults bound important dimensions of the search: at most 9 case splits per branch, 5 E-matching rounds before each split, theorem-instantiation generation 8, 1000 E-matching theorem instances per branch, and 10,000 iterations of the outer terminal action loop. Global Lean heartbeats and solver-specific step limits impose additional bounds.

`grind` has several extension layers, but they have different isolation and stability properties. Ordinary theorem-facing customization uses `[grind ...]` roles, explicit `grind_pattern` declarations, per-call parameters, and custom attributes created with `register_grind_attr`. A call can combine multiple custom grind attributes. Those attributes carry case-split types, extensionality theorems, function-congruence symbols, E-matching theorems, and injectivity theorems. They do **not** own independent normalization or symbol-priority sets: those are deliberately shared across grind attributes.

The lower-level extension mechanisms are more global. Solver extensions and builtin propagators can only be registered during initialization, and builtin propagators are shared by all grind attributes. These are implementation APIs, not evidence of a stable runtime plugin ABI.

`grind only` narrows the theorem environment but is not a hermetic “use only these facts and nothing else” mode. At the tactic entry point, it removes the default grind E-matching and injectivity theorem sets while retaining the default cases, function-congruence, and extensionality sets. It also continues to construct the global normalization context and simprocs, uses local hypotheses automatically, and leaves the configured theory solvers enabled. For generated proofs that need a narrower dependency surface, `only` is useful, but its meaning is specific to these implementation boundaries.

The pinned source explicitly exposes search instability as a concern. The optional `grind.warning` says that `grind` is new and its behavior may change, the E-matching implementation records that assertion order affects the proof found, and a checked-in heartbeat test is disabled because the exact timeout location can be nondeterministic. Generated scripts and proof-search success should therefore be revalidated at a new Lean revision rather than treated as a stable protocol.

No fresh Lean build or tactic execution was performed for this report. Findings come from exact pinned source and checked-in tests.

## Applicability

This report applies to Lean 4 commit `3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`, identified by the selected Anneal toolchain as `v4.30.0-rc2`.

The report covers four related surfaces:

1. the ordinary terminal `grind` tactic;
2. the interactive `grind => ...` inner tactic language and its `finish`/`finish?` search;
3. theorem-, pattern-, and attribute-level customization; and
4. source-level solver and propagator extension interfaces.

The report describes implementation behavior at this exact revision. It does not claim that search order, default limits, internal extension APIs, generated tactics, or proof-search success are stable across Lean releases.

Where the report says that a facility is “enabled by default,” it means the corresponding field in `Lean.Grind.Config` has the stated default at this revision. A caller can override those fields directly, through interactive `set_config`, or by using one of the specialized configurations such as the no-op, cutsat, linarith, order, or ring/Grobner configurations.

The source tree contains stage-0 generated C copies of much of the implementation. This report treats the Lean source as the primary implementation source and does not separately use the generated C as independent evidence.

## Findings

### Terminal `grind` runs a bounded search pipeline

The public tactic builds a `Grind.Params` value, initializes a protected metavariable context, and calls `Lean.Meta.Grind.main`. The meta-level entry point creates a fresh grind goal with `initCore`, asserts extra facts or theorem parameters, calls `solve`, and packages the result. If the resulting `Grind.Result` reports failure, the tactic raises `` `grind` failed ``; on success it replaces the current main goal with no goals.

The terminal search is assembled in `Lean.Meta.Grind.Action.mkFinish`:

```text
solvers <|> instantiate <|> splitNext <|> mbtc
```

That recurring step is wrapped by an initial tactic-consistency check, introduction of hypotheses, assertion of queued facts, and `step.loop maxIterations`. At this revision, `maxIterationsDefault` is 10,000 and has a source TODO to make it an option.

This order is operationally important. Registered solver actions get the first chance to make progress in each recurring step; E-matching instantiation comes next; then a case split; then model-based theory combination. The implementation is not simply a fixed sequence of one pass through each component: progress feeds back through the loop until the goal closes, the action becomes stuck, or a resource bound terminates the search.

**Evidence:** **source** — `src/Lean/Meta/Tactic/Grind/Main.lean`, `src/Lean/Meta/Tactic/Grind/Solve.lean`, and `src/Lean/Meta/Tactic/Grind/Finish.lean`.

### The action abstraction exists for backtracking and replayable proof scripts

`grind` represents a search step as a continuation-passing `Action`. Each action receives the current goal, a continuation for “not applicable,” and a continuation for “made progress.” It eventually returns either a closed result with a replayable sequence of grind tactics or a stuck result with residual goals.

The source explains two reasons for this design. First, branching actions such as `splitNext` can run the downstream continuation on each branch and use the resulting proofs to perform non-chronological backtracking. Second, actions can inspect the eventual proof and record only search operations that mattered to the successful result.

The solver wrapper illustrates the second property. When tracing is enabled, a solver that propagated facts first runs the continuation. If the downstream sequence already replays successfully from the pre-solver state, the solver step is omitted from the generated tactic sequence. Otherwise it is retained. The source says this is necessary, not merely an optimization: a superfluous solver step may depend on a case split that non-chronological backtracking later prunes, making the generated script fail to replay.

E-matching uses the same principle. `EMatchAction` marks theorem instances, examines the eventual proof term, collects theorem instances actually used by that proof, and constructs replay parameters from them. Its source also records that theorem assertion order affects the proof found, so it preserves original instantiation order when generating the replay tactic.

`finish?` exposes this machinery to users. It turns tracing on, runs `mkFinish`, constructs both an explicit tactic sequence and a compact `finish only [...]` form when possible, and checks the compact form by replay before offering it as a suggestion. Checked-in tests show suggestions such as case-split anchors followed by `ring`, `lia`, or `ac`, and compact `finish only` forms containing just the anchors and theorem parameters needed for replay.

**Evidence:** **source** — `src/Lean/Meta/Tactic/Grind/Action.lean`, `src/Lean/Meta/Tactic/Grind/EMatchAction.lean`, `src/Lean/Elab/Tactic/Grind/Trace.lean`; **source fixture** — `tests/elab/grind_finish_trace.lean`.

### Congruence closure and solver state share facts during search

The core maintains equivalence classes of expressions and propagates equalities through parent applications. Each equivalence-class root can also carry “solver terms” for the registered theory solvers. The implementation describes these as analogous to theory variables in SMT solvers. When two equality classes merge, the core merges their solver terms and asks the corresponding solvers to propagate the new relationship. New disequalities are likewise dispatched to solvers that have terms in both classes.

`GrindM` carries the ordinary grind state over `Sym.SymM`, and its state includes the simplifier state, congruence-theorem cache, diagnostics, anchors, and E-matching instance bookkeeping. Each grind goal also carries an array of registered solver-extension states.

The practical consequence is that solver procedures are not isolated post-processing tactics. They participate in the same evolving equality/fact state as theorem instantiation and congruence propagation.

**Evidence:** **source** — `src/Lean/Meta/Tactic/Grind/Types.lean` and `src/Lean/Meta/Tactic/Grind/Core.lean`.

### Default search breadth is controlled by explicit limits and switches

`Lean.Grind.Config` exposes the main search and solver controls. At this revision, important defaults include:

- `splits := 9`: maximum case splits in a proof-search branch, excluding normalization-time splits;
- `ematch := 5`: maximum E-matching rounds before each case split;
- `gen := 8`: maximum theorem-instantiation generation;
- `instances := 1000`: maximum E-matching theorem instances in a search branch;
- `canonHeartbeats := 1000`: thousands of heartbeats available to the canonicalizer for each definitional-equality test;
- `matchEqs := true`, `splitMatch := true`, and `splitIte := true`;
- `ext := true`, `etaStruct := true`, and `funext := true`;
- `mbtc := true`;
- `ring := true` with `ringSteps := 100000`;
- `linarith := true`;
- `lia := true`;
- `ac := true` with `acSteps := 1000`;
- `inj := true`;
- `order := true`;
- `funCC := true`.

The config also enables `zetaDelta` and `zeta` by default, uses reducible transparency when trying to close goals, and can optionally ask a library-suggestion engine for additional theorems or add all definitions from the current source file.

These limits do not form a complete resource budget. Lean's ordinary heartbeat mechanism still applies, and individual solver or canonicalizer operations may consume different amounts of work before a high-level grind counter changes. A checked-in test that attempted to pin a 5,000-heartbeat failure was commented out because it was nondeterministic whether the timeout occurred in `whnf` or `isDefEq`.

**Evidence:** **source** — `src/Init/Grind/Config.lean`; **source fixture** — `tests/elab/grind_heartbeats.lean`.

### Specialized configurations change the search components rather than replacing `grind`

The same config file defines a `NoopConfig` and narrower derived configurations. `NoopConfig` disables splitting, E-matching rounds, extensionality, function extensionality, function-valued congruence closure, and all listed solver modules. The source describes it as a starting point for minimal configurations.

`CutsatConfig`, `LinarithConfig`, and `OrderConfig` re-enable their corresponding reasoning procedure and the default split count. `GrobnerConfig` re-enables ring reasoning. The cutsat configuration contains an important qualification: cutsat still benefits from some theorem instantiation, and the source says there is currently no mechanism in that specialized configuration to enable only a small set of lemmas.

Interactive `set_config` can alter the same fields inside a `grind => ...` block. Checked-in tests vary `gen` and toggle linear integer arithmetic around individual inner tactics.

**Evidence:** **source** — `src/Init/Grind/Config.lean` and `src/Lean/Elab/Tactic/Grind/Config.lean`; **source fixture** — `tests/elab/grind_set_config.lean`.

### The default `[grind]` attribute records several different semantic roles

The default grind attribute is not one undifferentiated theorem set. `AttrKind` distinguishes:

- E-matching theorems, including several orientations and generation modes;
- case-split types, including eager splitting;
- `intro` and `infer` roles;
- extensionality declarations;
- symbol priorities;
- injectivity theorems;
- function-valued congruence symbols;
- normalization rules; and
- unfolding rules.

The E-matching role itself supports multiple directions and equality-side choices. Parameter and attribute syntax can select forward or backward reasoning, equality-left/equality-right/both forms, generation-producing variants, and user-specified patterns.

The default environment extension ultimately stores five categories in `ExtensionState`: case-split types, extensionality declarations, function-congruence symbols, E-matching theorems, and injectivity theorems. Normalization and symbol priorities are intentionally kept outside individual extension states and shared globally.

**Evidence:** **source** — `src/Lean/Meta/Tactic/Grind/Attr.lean` and `src/Lean/Meta/Tactic/Grind/Extension.lean`.

### `grind_pattern` gives explicit control over E-matching triggers

`grind_pattern` associates one or more explicit patterns with a theorem. Multi-patterns require the entire pattern set to match before instantiation. The command validates that patterns can determine required theorem parameters, and checked-in tests cover both accepted patterns and diagnostics for patterns that leave parameters uninstantiable.

A pattern can also carry constraints. At this revision the representation supports:

- definitional equality and disequality constraints;
- size and approximate-depth bounds on matched terms;
- theorem-instantiation generation bounds;
- per-theorem instance-count bounds;
- groundness tests;
- value and strict-value tests and their negations;
- `guard`, which delays instantiation until a proposition is known true; and
- `check`, which tests implication by asserting the negation.

The command may target the default `grind` attribute or another registered grind attribute. User-pattern selection through the `usr` parameter modifier has a narrower implementation boundary: the parameter elaborator explicitly says that this lookup is hard-coded to the default `grind` attribute and records custom-attribute support there as a possible improvement.

**Evidence:** **source** — `src/Lean/Meta/Tactic/Grind/Extension.lean`, `src/Lean/Meta/Tactic/Grind/Parser.lean`, `src/Lean/Elab/Tactic/Grind/Main.lean`, and `src/Lean/Elab/Tactic/Grind/Param.lean`; **source fixtures** — `tests/elab/grind_pattern1.lean` and `tests/elab/grind_pattern2.lean`.

### Custom grind attributes compose, but their normalizers do not isolate

`register_grind_attr foo` creates a new scoped environment extension and the corresponding attribute syntax. A grind parameter whose identifier resolves to such an extension appends that extension's state to the current `Params.extensions` array. The core is explicitly designed to scan a small array of extension states, so an invocation can combine multiple custom attributes instead of merging them into one global theorem set.

This composition has a deliberate limit. The source says all grind attributes currently share one normalization set and one symbol-priority set because E-matching patterns must be normalized consistently. Giving each attribute its own normalizer would require re-normalizing patterns against the union of normalizers when several attributes are active. The implementation chooses composable attribute sets with shared normalization instead.

Therefore a custom grind attribute can isolate its case/extensionality/function-congruence/E-matching/injectivity entries, but it is not a complete semantic sandbox for grind behavior.

**Evidence:** **source** — `src/Lean/Meta/Tactic/Grind/RegisterCommand.lean`, `src/Lean/Meta/Tactic/Grind/Attr.lean`, `src/Lean/Meta/Tactic/Grind/Extension.lean`, and `src/Lean/Elab/Tactic/Grind/Param.lean`.

### `grind only` narrows default theorem sets, not the whole proof engine

At the ordinary tactic entry point, `mkDefaultParams` loads the full default `grind` extension state. `mkOnlyParams` instead calls `getOnlyExtensionState`. That function takes the default state and retains only:

- case-split types;
- function-congruence symbols; and
- extensionality declarations.

It omits the default E-matching and injectivity theorem maps. Explicit parameters can then add the desired theorem or definition behavior.

The rest of parameter construction is shared. Both ordinary and `only` modes build the same normalization context, simprocs, and global symbol priorities from the current environment and config. The theory solvers are also controlled by the same `Grind.Config`; `only` does not set their toggles to false. Local hypotheses remain ordinary grind input. In the interactive `finish only` path, source comments also state that match-equation theorems and selected local theorem instances are intentionally retained.

This makes `only` a theorem-dependency narrowing mechanism, not a proof-engine isolation mode. If a generated proof must exclude solver modules or other search features, their config fields must be controlled separately.

Anchors provide another form of narrowing. Anchor parameters are accepted only with `only`, and checked-in `finish?` tests show compact proofs that retain only selected case splits or local theorem instances.

**Evidence:** **source** — `src/Lean/Meta/Tactic/Grind/Main.lean`, `src/Lean/Elab/Tactic/Grind/Param.lean`, and `src/Lean/Elab/Tactic/Grind/Main.lean`; **source fixture** — `tests/elab/grind_finish_trace.lean`.

### Per-call parameters can add, remove, or reinterpret declarations

At the tactic entry point, parameters can add named declarations or proof terms as E-matching input, select a grind modifier, require the “minimal indexable” pattern mode with `!`, remove an existing default entry with `-`, add a registered custom grind attribute by name, or select anchors in `only` mode.

The parameter elaborator infers a role when no modifier is supplied. A definition can contribute generated equation theorems. An inductive type can contribute case behavior. A proof term whose type is a `forall` can be converted into an E-matching theorem; a non-`forall` proposition is added as a fact. Local hypotheses do not need to be named as parameters because `grind` uses them automatically.

Some modifiers require global declarations. The source rejects cases, intro, injectivity, extensionality, symbol, function-congruence, normalization, and unfold modifiers on arbitrary local proof terms. When `+revert` is active, only global declaration parameters are accepted.

The `lax` config changes parameter-error handling: invalid or unresolved parameters can be silently ignored rather than aborting elaboration.

**Evidence:** **source** — `src/Lean/Elab/Tactic/Grind/Param.lean`.

### Lower-level solver extensions are global initialization-time registrations

`SolverExtension` is a lower-level interface for a theory module. An extension owns per-goal state and handlers for:

- expression internalization;
- newly discovered equalities;
- newly discovered disequalities;
- model-based theory combination;
- a search `Action`;
- a consistency/check operation; and
- invariant checking.

`registerSolverExtension` allocates the extension a numeric slot in every goal's solver-state array. `SolverExtension.setMethods` fills in its handlers. Both functions reject calls outside Lean initialization, and the source gives the reason: the global extension registry is accessed without a synchronization primitive.

The registered solver actions are combined into one action with `Action.andAlso`. Fact propagation through the core dispatches equalities and disequalities to registered solver extensions that have marked corresponding solver terms.

This is a real extension interface in the pinned implementation, but its initialization restriction and private global registry make it qualitatively different from a dynamic plugin protocol. Nothing in the inspected source establishes a compatibility guarantee for external code across Lean versions.

**Evidence:** **source** — `src/Lean/Meta/Tactic/Grind/Types.lean` and `src/Lean/Meta/Tactic/Grind/Intro.lean`.

### Builtin propagators are also initialization-time and shared globally

`grind` has separate upward and downward builtin-propagator maps keyed by declaration name. The core's methods first perform several standard propagations, then invoke registered builtin propagators for the head declaration.

Registration is allowed only while Lean is initializing. The propagator source also states that the same builtin propagators are currently used for all grind attributes. Unlike a custom `register_grind_attr`, a propagator cannot create an isolated per-attribute behavior set.

The builtin propagator attribute itself is registered for `afterCompilation`, and its erase operation is not implemented at this revision.

**Evidence:** **source** — `src/Lean/Meta/Tactic/Grind/PropagatorAttr.lean` and `src/Lean/Meta/Tactic/Grind/Main.lean`.

### Interactive mode exposes the search engine as a small tactic language

`grind => ...` enters `GrindTacticM` instead of immediately running the terminal search. The checked-in sources and tests expose operations such as `finish`, `finish?`, `cases_next`, solver steps such as `lia` and `ring`, explicit theorem instantiation, model-based theory combination, `have`, repetitions/choice, and local config changes.

Interactive mode uses `ConfigInteractive`, which changes `clean` to false. That matters because the interactive language refers to anchors and local names that must remain stable enough for the generated/replayed script. The terminal parameter builder likewise disables `clean` when anchor references are present because cleaning hypothesis IDs would change anchor values.

The inner language is therefore not just syntax sugar around repeated top-level `grind` calls. It shares the same evolving grind goal and state while giving callers explicit control over which search action runs next.

**Evidence:** **source** — `src/Lean/Elab/Tactic/Grind/Basic.lean`, `src/Lean/Elab/Tactic/Grind/Main.lean`, `src/Lean/Elab/Tactic/Grind/Config.lean`, and `src/Init/Grind/Config.lean`; **source fixtures** — `tests/elab/grind_set_config.lean` and `tests/elab/grind_finish_trace.lean`.

### Generated tactics are replay-checked, but search choice is not a stable protocol

The tracing implementation takes deliberate steps to generate a smaller replayable proof. It can drop solver actions that turn out not to be needed, reduce E-matching parameters to theorem instances used by the final proof, collect case-split anchors, and check whether a compact `finish only [...]` replay closes the original goal before suggesting it.

These mechanisms improve robustness of a generated script against irrelevant search activity. They do not make the search result stable across versions. The source states that theorem assertion order affects the proof found. The optional `grind.warning` emits: “The `grind` tactic is new and its behavior may change in the future.” The disabled heartbeat regression test separately documents nondeterminism in the location of a timeout.

For an agent that generates Lean annotations, the useful distinction is between two artifacts:

- a proof term or replay script that Lean has checked at this exact revision; and
- an assumption that rerunning unconstrained `grind` later will choose the same search path.

The first can be durable if its dependencies remain available. The second is not established by this implementation.

**Evidence:** **source** — `src/Lean/Meta/Tactic/Grind/Action.lean`, `src/Lean/Meta/Tactic/Grind/EMatchAction.lean`, `src/Lean/Elab/Tactic/Grind/Trace.lean`, and `src/Lean/Elab/Tactic/Grind/Main.lean`; **source fixture** — `tests/elab/grind_heartbeats.lean`.

## Boundaries

- No fresh Lean executable was built or run. All behavioral claims are source-derived and, where noted, cross-checked against checked-in tests.
- This report does not measure `grind` performance, memory use, proof-term size, or success rates on Anneal-generated goals.
- The listed default limits do not imply deterministic run time. Lean heartbeats, definitional equality, elaboration, and individual solver operations impose additional costs that do not map one-to-one to `grind`'s high-level counters.
- The report does not claim completeness for any solver module or for `grind` as a whole.
- The report does not claim that `grind only` eliminates all implicit dependencies. Source establishes the opposite: normalization, builtins, local facts, selected structural attribute state, and configured solvers remain relevant.
- `register_grind_attr` provides a source-supported customization surface, but independent per-attribute normalization and symbol priorities are known not to apply at this revision.
- Solver-extension and builtin-propagator registration are known to be initialization-only. This report does not establish whether external packages should rely on those APIs as stable public interfaces.
- The symbolic-simplifier `sym_simproc`/`sym_discharger` elaboration DSL exists in the interactive grind implementation, but this report does not attempt a complete account of its syntax or semantic contract.
- The report does not establish byte-for-byte or tactic-for-tactic determinism of `finish?` suggestions. Checked-in source specifically records order sensitivity and a nondeterministic timeout case.
- The report does not infer behavior for Lean versions before or after `v4.30.0-rc2`.

## Evidence

All Lean source below is from `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (`v4.30.0-rc2`). Evidence was inspected on 2026-09-27.

**Source:**

- `src/Init/Grind/Config.lean`, blob `5eb9a2c63660ca5c972a9a6fd62bdb290d7ceda1`: `Grind.Config` defaults; no-op and specialized configurations; solver and search switches; function-valued congruence behavior.
- `src/Lean/Elab/Tactic/Grind.lean`, blob `cb94b6d3c0d4769ad1a955865b565eace513b75f`: public grind module surface.
- `src/Lean/Elab/Tactic/Grind/Main.lean`, blob `ed3e9d3c5f0714b5e639a8ec4b363e1e18f0440a`: tactic entry point; parameter construction; custom patterns; suggestions/locals; success/failure behavior; instability warning.
- `src/Lean/Elab/Tactic/Grind/Basic.lean`, blob `228ff2bfa68af17189054af1d6ad7cffc2f8921b`: interactive `GrindTacticM` state and context.
- `src/Lean/Elab/Tactic/Grind/Config.lean`, blob `77284d85bbda62caf861ef79581964d5d2f18a7d`: interactive config mutation.
- `src/Lean/Elab/Tactic/Grind/Param.lean`, blob `38087c6f152b5dd27403daa0289361d3c85ff7f4`: per-call parameter semantics, custom-attribute inclusion, `only`, anchors, removal, and local proof-term handling.
- `src/Lean/Elab/Tactic/Grind/Trace.lean`, blob `ee030a6181b6193c49d89905ac4b350a1df4edcb`: `finish?` tracing and replay-checking of compact suggestions.
- `src/Lean/Elab/Tactic/Grind/SimprocDSL.lean`, blob `6a6b27e6d9b48bd7c267e8c5a42b970a49bc746a`: symbolic simp/discharger elaborator extension hooks.
- `src/Lean/Meta/Tactic/Grind/Main.lean`, blob `25a9f455f2c2dd07750452ad756d3de926b69238`: parameter/environment initialization, shared normalization context, builtin propagator methods, goal setup, and meta entry point.
- `src/Lean/Meta/Tactic/Grind/Solve.lean`, blob `a1c679096c93ec97eaee4569a7e176dcd4744467`: terminal solve wrapper around `Action.mkFinish`.
- `src/Lean/Meta/Tactic/Grind/Finish.lean`, blob `6bae01e1c2c4772d0cabe99ff74437492ccebfc5`: terminal search ordering and 10,000-iteration default.
- `src/Lean/Meta/Tactic/Grind/Action.lean`, blob `ad212d7c8ef8277b4be3650d43738ee98a32cbf5`: CPS action contract, non-chronological backtracking rationale, solver-step replay minimization.
- `src/Lean/Meta/Tactic/Grind/EMatchAction.lean`, blob `fc52108c3bc3a2ecdb7e54b4b1c1a13365d5e9b6`: proof-relevant theorem-instance collection and order-sensitive replay construction.
- `src/Lean/Meta/Tactic/Grind/Core.lean`, blob `bf4b53bc27f0c8bfd76d0e9e0c749f77a54a4432`: equality-class merging and propagation into theory solvers.
- `src/Lean/Meta/Tactic/Grind/Types.lean`, blob `6b4e740c1ff57178c6478e1f614e916c2da91441`: Grind state, solver terms, `SolverExtension`, initialization-only registration, and solver-action composition.
- `src/Lean/Meta/Tactic/Grind/Extension.lean`, blob `ec1142df21e3276a30042a137003e842e67f0595`: E-matching kinds/constraints, extension state, custom-attribute composition, and shared-normalization design boundary.
- `src/Lean/Meta/Tactic/Grind/Attr.lean`, blob `f54e02fb7c4f37677056e2cb0737774fd3b051b3`: grind attribute kinds and registration.
- `src/Lean/Meta/Tactic/Grind/RegisterCommand.lean`, blob `6e2267f83d496f1e7448e7ebf98c3888366e2f59`: `register_grind_attr` macro.
- `src/Lean/Meta/Tactic/Grind/PropagatorAttr.lean`, blob `77e0ab069bf9277ead3008e315199e06addd09d0`: builtin propagator maps, initialization-only registration, and global sharing across grind attributes.
- `src/Lean/Meta/Tactic/Grind/ExtAttr.lean`, blob `025b7c1bba1f05acb923cad7239cac72e234f1bd`: validation of `[grind ext]` declarations.
- `src/Lean/Meta/Tactic/Grind/Parser.lean`, blob `a3657438ed7a6bde1a9f88108ba1eae4e7ea5f30`: explicit-pattern constraint grammar.
- `src/Lean/Meta/Tactic/Grind/Split.lean`, blob `b7651d19b7da21c55be86f802e5fec01dbead4d5`: split status and non-chronological backtracking support.

**Checked-in source fixtures:**

- `tests/elab/grind_attrs.lean`, blob `36515bf3455603f41b7dbb5a71e48fcd4798e5a2`: E-matching attribute direction syntax and `grind only` examples.
- `tests/elab/grind_pattern1.lean`, blob `6b778d12d7f57891c1a8780f109da7f48c8fd834`: explicit pattern validation and multi-pattern examples.
- `tests/elab/grind_pattern2.lean`, blob `3b7e8bb0b34dd3cba833bed837e38917e229f8f4`: explicit pattern activation examples.
- `tests/elab/grind_set_config.lean`, blob `0fb2e489b8b70759ce024a28a8863f4d3fec1827`: interactive config changes, `finish`, and `finish?`.
- `tests/elab/grind_finish_trace.lean`, blob `7356d0ecf4ec63ac196a9404e7ec2e4807d96976`: generated explicit/compact replay suggestions, anchors, theorem instantiation, solver steps, and model-based theory combination.
- `tests/elab/grind_heartbeats.lean`, blob `3ca561c130ba7d001ae6394292520c5403a88b0f`: disabled regression test documenting nondeterministic timeout location.

There is no fresh **execution** evidence in this report.

## Revalidation

For another Lean revision, first diff the small set of control points that determine the architecture:

1. `src/Lean/Meta/Tactic/Grind/Finish.lean` for terminal action ordering and the outer iteration limit;
2. `src/Init/Grind/Config.lean` for default search limits, solver toggles, and specialized configurations;
3. `src/Lean/Meta/Tactic/Grind/Main.lean` and `src/Lean/Elab/Tactic/Grind/Main.lean` for goal initialization, terminal success/failure, and parameter construction;
4. `src/Lean/Elab/Tactic/Grind/Param.lean` for `only`, anchor, custom-attribute, and per-call parameter semantics;
5. `src/Lean/Meta/Tactic/Grind/Extension.lean`, `Attr.lean`, and `RegisterCommand.lean` for theorem-facing extension-state shape and isolation boundaries;
6. `src/Lean/Meta/Tactic/Grind/Types.lean` and `PropagatorAttr.lean` for solver/propagator registration lifetime and global sharing; and
7. `src/Lean/Meta/Tactic/Grind/Action.lean`, `EMatchAction.lean`, and `src/Lean/Elab/Tactic/Grind/Trace.lean` for backtracking and generated-script replay behavior.

If execution is available, a small discriminating fixture can then test the most integration-sensitive claims:

- register two custom grind attributes, place distinct E-matching theorems in each, and show that one invocation can combine both;
- compare plain `grind`, `grind only []`, and a no-op config on a goal solvable by a default theory solver to distinguish theorem narrowing from solver disabling;
- add an explicit `grind_pattern` with a multi-pattern and a constraint and confirm its activation boundary;
- run `grind => finish?` on a goal that needs a split plus a solver and verify that the suggested compact `finish only [...]` replay closes the original goal;
- reduce `splits`, `ematch`, `gen`, or `instances` below the amount required by a tiny synthetic proof and confirm failure at the intended search bound; and
- if testing extension APIs, attempt solver or builtin-propagator registration only during initialization and confirm that runtime registration remains rejected.

Do not use exact `finish?` suggestion text or an exact timeout site as a golden cross-version compatibility test. The pinned source itself says theorem assertion order affects the proof found, and the checked-in heartbeat test records nondeterministic timeout location. Revalidate semantic closure and the extension/search boundary instead.