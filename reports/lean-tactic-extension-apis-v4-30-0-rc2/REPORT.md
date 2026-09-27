# Lean tactic extension APIs at v4.30.0-rc2

## Summary

Lean's tactic extension surface at `v4.30.0-rc2` is a layered pipeline rather than one registry. A custom tactic normally combines a parser entry, an optional macro expander, and/or a tactic elaborator. The high-level commands are `syntax ... : tactic`, `macro`/`macro_rules`, and `elab`/`elab_rules : tactic`; direct use of the underlying parser and elaborator attributes exists, but Lean's own source explicitly recommends the higher-level commands for ordinary extensions.

The governing distinction is between **syntax transformation** and **goal-state execution**. A tactic macro is a `Lean.Macro`: it transforms syntax in `MacroM` and does not itself run in tactic state. A tactic elaborator is a `Lean.Elab.Tactic.Tactic`, exactly `Syntax → TacticM Unit`; `TacticM` extends term elaboration with a current goal list and a small tactic reader context. A tactic can therefore inspect and replace goals, invoke `MetaM` operations, elaborate terms, and recursively call `evalTactic` on generated tactic syntax.

For one tactic syntax node kind, Lean may have multiple macro expanders and multiple tactic elaborators. At this revision, `evalTactic` tries **all macros before all tactic elaborators**, restoring saved elaboration/tactic state between failed candidates. Ordinary elaboration errors, abort-tactic exceptions, and unsupported-syntax results can all lead to another candidate; only unsupported-syntax failures are omitted from the saved failure list. If no candidate succeeds, Lean restores the selected saved failure state and rethrows an error, or reports unexpected syntax if there was no retained failure. This means an extension point is intentionally a backtracking chain, not a single function slot.

Both parser registrations and non-builtin tactic-elaborator registrations are environment-backed and serializable through `.olean` import state. Their serialized forms store declaration identities and registration metadata, not arbitrary closures; the imported environment reconstructs executable parser/elaborator values from those declarations. Consequently, a reusable Anneal tactic extension should live in a module that generated proof files import. It does not require modifying Lean itself, and it does not introduce a new kernel rule: ordinary tactic code generates or assigns proof terms/metavariables that remain subject to Lean's later checking. Operationally, however, tactic code is metaprogram execution and can perform arbitrary effects permitted by its monad/runtime, so kernel soundness and build reproducibility remain separate questions.

No fresh Lean process was executed for this report. Findings come from exact source inspection at `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` plus pinned regression tests from that same revision.

## Applicability

This report covers the tactic-extension machinery shipped in Lean `v4.30.0-rc2`, revision `3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`, which is the Lean revision selected by current Anneal source. It focuses on extension mechanisms useful to generated or maintained Anneal proof scripts:

- declaring tactic grammar;
- lowering custom tactic syntax through macros;
- implementing custom tactic elaborators in `TacticM`;
- composing extensions with existing tactics and `MetaM` operations;
- registration, import, scoping, fallback, and incremental-elaboration behavior;
- what state and provenance Lean records when an extension executes.

It does not inventory the specialized extension systems inside individual tactics such as `simp`, `grind`, or `omega`; those have separate registries and are better treated by their own reports. It also does not claim source-level API stability across Lean releases. These extension APIs are implementation-facing Lean metaprogramming interfaces whose exact names, monad stack, fallback rules, and incremental protocol should be rechecked when the Lean pin changes.

## Findings

### A tactic extension has three independent layers: parser, macro, and elaborator

The normal source-level path is:

1. `syntax ... : tactic` registers grammar that produces a syntax node kind in the `tactic` category.
2. `macro` or `macro_rules` may associate that syntax kind with one or more `Lean.Macro` expanders that produce replacement syntax.
3. `elab ... : tactic => ...` or `elab_rules : tactic` may associate the syntax kind with one or more `Lean.Elab.Tactic.Tactic` elaborators that execute against proof state.

These layers are independent. A tactic can be macro-only, elaborator-only after declaring syntax, or have both. The pinned `tests/elab/macroElabRulesIssue1.lean` deliberately combines both for the same `Foo` syntax: an identifier case is handled by a macro, while a numeric case is handled by an `elab_rules : tactic` elaborator. The existence of both is therefore an intended extension pattern, not just an internal implementation detail.

Basis: pinned Lean **source** in `Lean.Elab.Syntax`, `Lean.Elab.MacroRules`, `Lean.Elab.ElabRules`, and **execution-fixture source** in `tests/elab/macroElabRulesIssue1.lean`.

### `syntax ... : tactic` registers a parser in a scoped environment extension

The tactic syntax category is registered with a builtin parser attribute and an extendable dynamic `tactic_parser` attribute. User `syntax` declarations are elaborated into meta parser declarations tagged with the category's parser attribute. The command accepts a parser priority and computes a syntax-node kind from the current namespace and declared or synthesized name.

The parser subsystem stores user/parser registrations in `parserExtension`, a `ScopedEnvExtension`. Its state includes tokens, syntax-node kinds, and parser categories. A parser registration records the category, declaration name, whether it is a leading or trailing parser, the executable parser, and priority. The `.olean` form stores only category, declaration name, and priority; import reconstructs the parser from the named declaration with `mkParserOfConstant`.

This has two practical consequences for Anneal. First, custom syntax is module/environment state: a downstream generated proof file gets the extension by importing or activating the module/scope that carries the registration. Second, the extension is not a process-global anonymous closure that must be reinstalled manually after each import; the declaration identity is sufficient to reconstruct it from the imported environment.

The parser extension is scoped. Ordinary exported declarations become available through imports; `local` declarations are deliberately non-exporting, and scoped registrations require the corresponding scope to be active. Generated proof syntax should therefore avoid relying accidentally on a local or unactivated scoped parser.

Basis: pinned Lean **source** in `src/Lean/Parser/Extension.lean`, `src/Lean/Parser/Term/Basic.lean`, and `src/Lean/Elab/Syntax.lean`.

### `macro_rules` is syntax rewriting, not proof-state execution

Lean's macro registry stores declarations of type `Lean.Macro`, which is a syntax-to-syntax computation in `MacroM`. `macro_rules` generates an auxiliary `Macro` declaration and attaches it to the relevant syntax node kind through the `macro` keyed-declarations attribute. Pattern alternatives that do not match throw the macro-level unsupported-syntax exception, which permits another rule to be tried.

A macro can generate ordinary tactic syntax and thereby delegate proof work to existing or custom tactic elaborators. The pinned `tests/elab/extensibleTacticBug.lean` and `tests/elab/evalTacticBug.lean` both declare one tactic syntax kind with multiple `macro_rules`; different rules lower the same surface tactic to `decide`, `assumption`, `apply ...`, or `contradiction` depending on which expansion succeeds downstream.

Because a macro runs in `MacroM`, it does not directly own the `TacticM` goal list. This makes macros appropriate for syntactic sugar and reusable lowering. Anything that must inspect the current goal, local context, metavariables, or term-elaboration state belongs in a tactic elaborator instead.

Basis: pinned Lean **source** in `src/Lean/Elab/MacroRules.lean` and `src/Lean/Elab/Util.lean`, plus pinned **execution-fixture source** in the two regression tests above.

### `Tactic` is exactly `Syntax → TacticM Unit`

At this revision, Lean defines:

- `TacticM := ReaderT Tactic.Context (StateRefT Tactic.State TermElabM)`;
- `Tactic := Syntax → TacticM Unit`;
- `Tactic.State` contains the current `List MVarId` goals;
- `Tactic.Context` records the executing elaborator name and an error-recovery flag.

The monad therefore inherits term-elaboration and meta-level facilities while adding explicit tactic goal state. Core helpers expose the goal list (`getGoals`, `setGoals`, `getMainGoal`, `replaceMainGoal`, `pushGoal`, `appendGoals`), context-sensitive meta execution, state save/restore, and recursive tactic evaluation.

This boundary is useful for Anneal architecture. A custom tactic that merely orchestrates generated proof steps can remain ordinary Lean metaprogramming code: it receives parsed syntax, reads/manipulates metavariable goals, and eventually leaves proof terms assigned to those goals. The extension API itself does not require a new elaboration protocol or an external process boundary.

Basis: pinned Lean **source** in `src/Lean/Elab/Tactic/Basic.lean` and `src/Lean/Elab/Term/TermElabM.lean`.

### `elab` and `elab_rules : tactic` are the preferred registration surface

`tacticElabAttribute` is a `KeyedDeclsAttribute Tactic`. Its builtin and ordinary attribute names are `builtin_tactic` and `tactic`. The source documentation says a tactic elaborator must have type `Lean.Elab.Tactic.Tactic` and explicitly recommends `elab_rules` and `elab` over direct attribute use.

For the `tactic` and `conv` syntax categories, `elab_rules` generates an auxiliary declaration of type `Lean.Elab.Tactic.Tactic` and applies the `tactic` attribute keyed by syntax node kind. `elab ... : tactic => rhs` is a convenience that first declares syntax and then expands to the corresponding `elab_rules` registration. Its optional `priority := ...` controls the generated **parser** declaration's priority; the tactic elaborator registry itself is a keyed list rather than a numeric-priority table.

`elab_rules` does not generically support every arbitrary user-defined syntax category. The pinned implementation has dedicated cases for term, command, tactic/conv, and do-elements; its own comment says users who need other categories can define a wrapper macro that uses this command as a fallback. That boundary should not be generalized into a claim that `elab_rules` is an arbitrary-category plugin framework.

Basis: pinned Lean **source** in `src/Lean/Elab/Tactic/Basic.lean`, `src/Lean/Elab/ElabRules.lean`, and `src/Lean/Elab/Syntax.lean`.

### Multiple implementations of one tactic kind form a backtracking chain

The source-level contract on `Tactic` says a syntax kind may have multiple associated tactic implementations and that they are attempted until one succeeds. The concrete evaluator is stronger and more specific.

For a non-null tactic syntax node, `evalTactic` retrieves both:

- `macroAttribute.getEntries env stx.getKind`; and
- `tacticElabAttribute.getEntries env stx.getKind`.

It saves tactic/elaboration state once, then calls `expandEval`, which tries the macro list first and only then enters the tactic-elaborator list. Each failed candidate restores the saved state before the next one. A normal `Exception.error` is retained as a candidate failure and causes fallback. The internal unsupported-syntax exception causes fallback without being retained. The internal abort-tactic exception is retained and also causes fallback. Other internal exceptions escape immediately.

If all candidates fail, Lean restores the state associated with the retained failure it chooses and rethrows that exception; if no retained failure exists, it reports unexpected syntax. Thus an implementation that reports a normal elaboration error does not necessarily terminate dispatch when older/other implementations remain. Extensions that intend exclusive handling should not assume "throwError commits this implementation" at this pin.

The keyed-declarations table itself prepends newly added same-key entries to its list. That explains why multiple rules are naturally tried as an extension chain, but imported-module merge ordering is an implementation detail of environment extensions and should not be treated as a cross-version semantic contract. Generated Anneal proofs should avoid depending on fragile relative ordering among unrelated modules' extensions of the same syntax kind.

Basis: pinned Lean **source** in `src/Lean/Elab/Tactic/Basic.lean` and `src/Lean/KeyedDeclsAttribute.lean`.

### Macros take precedence over tactic elaborators for the same syntax kind

`evalTactic` calls `expandEval` with the macro list and elaborator list, and `expandEval` exhausts macro candidates before it calls the elaborator dispatcher. This is observable in the pinned mixed macro/elaborator regression fixture: the macro handles `Foo ident`, while the elaborator remains available for `Foo num` after the macro declines that syntax.

This precedence matters when designing an extensible Anneal surface. Adding a macro for an already elaborated syntax kind can intercept syntax before existing tactic elaborators see it. Conversely, a macro that throws unsupported syntax leaves the elaborator chain available. A custom extension should use a distinct syntax kind unless intentional interposition is part of the interface.

Basis: pinned Lean **source** in `src/Lean/Elab/Tactic/Basic.lean` and pinned **execution-fixture source** in `tests/elab/macroElabRulesIssue1.lean`.

### Tactic dispatch records elaborator provenance in the info tree

`Tactic.Context` carries the currently executing elaborator declaration name. `evalTactic` installs that name before running either a macro or tactic elaborator and wraps execution in a tactic-info context. `mkTacticInfo` records the elaborator name, syntax, metavariable context before and after, and goals before and after.

For non-builtin macro/elaborator declarations, dispatch also calls `recordExtraModUseFromDecl (isMeta := true)` after successful use. This is build/dependency provenance for meta execution: a source file that uses an imported extension can record an extra module use associated with the declaration that actually handled the syntax.

For Anneal, this gives two useful observability points. Interactive tooling can identify the elaborator and before/after goal states through the info-tree machinery, and the build system has a hook to account for meta dependencies that are discovered through dispatch rather than direct term references.

Basis: pinned Lean **source** in `src/Lean/Elab/Tactic/Basic.lean` and `src/Lean/Elab/Util.lean`.

### Extension declarations survive module import by identity, not by serializing closures

Both relevant registry implementations are designed around the fact that executable Lean functions cannot simply be serialized into `.olean` files.

`KeyedDeclsAttribute.OLeanEntry` stores a key and declaration name. On import, the scoped environment extension evaluates the named declaration at the expected type to reconstruct the `Tactic` or `Macro` value. `ParserExtension.OLeanEntry` similarly stores parser registration metadata and reconstructs the parser from the declaration when importing it.

This is the durable module contract for custom tactics. The generated proof file need not recreate registry calls by hand; it must import the module containing the exported declarations and registrations. Reproducibility still depends on the exact imported module bytes/source and Lean revision, because the executable metaprogram is reconstructed from that environment.

Basis: pinned Lean **source** in `src/Lean/KeyedDeclsAttribute.lean` and `src/Lean/Parser/Extension.lean`.

### Incremental tactic reuse is opt-in for user elaborators

At this revision, tactic execution participates in Lean's incremental elaboration machinery, but arbitrary tactic extensions do not automatically receive a reusable tactic snapshot. Before running an elaborator, `evalTactic` checks `isIncrementalElab evalFn.declName`; non-incremental elaborators run under `withoutTacticIncrementality`. The corresponding helper recognizes declarations tagged with the builtin incremental mechanism or the ordinary `incremental` attribute.

Macros have a separate incremental path in `evalTactic` when there is exactly one remaining macro branch and no tactic elaborators, allowing the macro expansion and nested tactic snapshot to be reused under strict state checks. This is an implementation-level optimization, not a guarantee that arbitrary custom tactic code is restart-safe.

For an interactive Anneal extension, the safe default is therefore to treat custom elaboration as non-incremental until the code deliberately satisfies Lean's incremental contract and is annotated accordingly. Correctness should not depend on whether the server can reuse a prior tactic snapshot.

Basis: pinned Lean **source** in `src/Lean/Elab/Tactic/Basic.lean` and the `isIncrementalElab` implementation in `src/Lean/Elab/Term.lean`.

### Error recovery can admit goals; extension correctness must distinguish recovery from success

`Tactic.Context.recover` defaults to true. Core recovery helpers can log an exception and assign a labeled `sorry` to a failed goal, and unsolved-goal reporting also admits remaining goals after reporting the error. Individual tactic combinators can disable recovery with `withoutRecover` when backtracking semantics require a hard failure.

This does not mean every failed custom tactic silently succeeds: ordinary exceptions propagate through the dispatcher unless a recovery helper explicitly handles them, and final diagnostics still matter. It does mean that a tool consuming Lean tactic results must distinguish "elaboration produced a recoverable artifact with errors/sorries" from "the intended theorem was checked without admissions." The custom-tactic extension surface does not erase that broader Lean trust boundary.

Basis: pinned Lean **source** in `src/Lean/Elab/Tactic/Basic.lean`; broader admission/trust semantics belong to the separate Lean trust reports.

### A custom Anneal tactic does not need to become a kernel primitive

The extension mechanism runs before kernel acceptance. Tactic elaborators manipulate metavariables and construct/assign expressions; macros rewrite syntax to code that does the same. The final declaration is still checked according to Lean's ordinary declaration/kernel path unless some separate unchecked/admission mechanism is invoked.

This makes a custom tactic a suitable abstraction boundary for generated proof scripts when the goal is to stabilize proof-generation syntax or centralize recurring proof search. It can reduce generated-source coupling to low-level tactic sequences without expanding Lean's logical primitive set.

That conclusion is only logical, not operational. A tactic elaborator is executable metaprogram code and may use `IO`-capable infrastructure through the elaboration stack, invoke `unsafe` code such as existing `run_tac` machinery, read environment state, or otherwise affect reproducibility. Anneal should therefore pin and version custom tactic modules just as it pins other build-time tooling even though ordinary resulting proof terms remain kernel checked.

Basis: **derived** from the pinned tactic monad/dispatch source and Lean's existing separation between elaboration and declaration checking.

## Boundaries

- No fresh Lean build, parser invocation, tactic execution, LSP session, or incremental-reuse experiment was performed.
- The report describes Lean `v4.30.0-rc2` exactly; it does not promise that later Lean releases preserve these source-level APIs or fallback details.
- It does not inventory every method inherited by `TacticM` from `TermElabM`, `MetaM`, `CoreM`, or `IO` lifting. The important structural fact is the monad stack and explicit goal state.
- It does not inventory specialized tactic-specific plugins such as simp theorems/simprocs, grind extensions, omega internals, tactic documentation tags, try-tactic registries, or pretty-printer extensions.
- Parser **priority** and tactic elaborator **dispatch order** are different mechanisms. `syntax (priority := ...)` affects Pratt parser selection. The generic `tactic` keyed-declarations attribute has no numeric priority argument at this pin.
- Same-kind candidate order inside current keyed-declarations state follows current insertion/import behavior. This report does not elevate relative ordering across independently imported modules into a stable public contract.
- Macros run before tactic elaborators for the same syntax kind in the pinned `evalTactic`; this is not claimed as a theorem about future versions.
- Successful tactic elaboration is not equivalent to an admission-free proof. Error recovery can create labeled sorries, and separate Lean mechanisms can introduce axioms or unchecked behavior. Proof consumers need the trust checks documented elsewhere in the corpus.
- A custom tactic's imported registration is available only when the relevant module/scope is available. Local/scoped parser registrations have their ordinary environment/scoping semantics.
- This report does not establish server/LSP behavior around live edits of extension modules. The server, document lifecycle, cancellation, and long-lived cache behavior have separate inventory items.

## Evidence

Observed 2026-09-27.

**Primary subject.** `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (`v4.30.0-rc2`).

**Tactic monad and dispatcher — source.** `src/Lean/Elab/Tactic/Basic.lean`, blob `8c3f1c62b58a064eee9f5b1f2a71218ca741e2cf`.

This file defines `TacticM`, `Tactic`, `tacticElabAttribute`, goal-state helpers, tactic info, `evalTactic`, macro-before-elaborator dispatch, state restoration, recovery behavior, nested `evalTactic`, and incremental gating.

**Tactic state — source.** `src/Lean/Elab/Term/TermElabM.lean` at the primary revision. It defines `Tactic.State` with the current `List MVarId` goals.

**Generic elaborator and macro registry — source.** `src/Lean/Elab/Util.lean`, blob `73162ffa9085ffc879226d60a92aaff897494154`. `mkElabAttribute` constructs the keyed elaborator attributes; `macroAttribute` is the corresponding `Lean.Macro` registry; `expandMacroImpl?` shows macro fallback on unsupported syntax.

**Keyed declaration serialization and ordering — source.** `src/Lean/KeyedDeclsAttribute.lean`, blob `69705ed1915d832160f22d456208cc6299099e74`. The table stores lists keyed by syntax node kind, new entries are prepended, `.olean` entries contain key/declaration name, and import reconstructs values with `evalConstCheck`.

**High-level elaborator commands — source.** `src/Lean/Elab/ElabRules.lean`, blob `82b1b8a6b318efebd8196ef7b585ffcbb5e453c2`. It lowers `elab_rules : tactic`/`conv` to auxiliary `Tactic` declarations with the `tactic` attribute and implements `elab` as syntax plus elaborator registration.

**High-level macro commands — source.** `src/Lean/Elab/MacroRules.lean`, blob `e72126f5b4c2475a97249c44ca5299f5d9c41c2d`. It lowers `macro_rules` to auxiliary `Lean.Macro` declarations registered by syntax node kind.

**Syntax declaration lowering — source.** `src/Lean/Elab/Syntax.lean`, blob `4080384e345659536cef7648001a19e68619720a`. It constructs parser declarations, node kinds, parser priorities, and parser attributes for `syntax` commands.

**Parser environment extension — source.** `src/Lean/Parser/Extension.lean`, blob `df40e6545cfa3ce19d68c80ef331e57aa6dd0439`. It defines `ParserExtension` as a scoped environment extension, its serialized entry form, parser reconstruction, user parser attributes, parser priorities, token/kind tracking, and scoped activation.

**Tactic category registration — source.** `src/Lean/Parser/Term/Basic.lean`, blob `a0d7ffe4bacfba3ecbf85a189ca5d010e5468377`. It registers the builtin tactic parser category and the user-extendable `tactic_parser` attribute.

**Builtin tactic examples — source.** `src/Lean/Elab/Tactic/BuiltinTactic.lean`, blob `7ad5c491440bcb3a5235047e9faf3b1b8540d44e`. Builtins use `@[builtin_tactic ...]`, recurse through `evalTactic`, manipulate goals, and include the `run_tac` bridge to evaluated `TacticM` code.

**Mixed macro/elaborator fixture — source at the primary revision.** `tests/elab/macroElabRulesIssue1.lean`, blob `f511da52e6fd22ebd622a78055d7bde05d1549ac`. One `Foo` tactic syntax kind has a numeric `elab_rules` case and an identifier `macro_rules` case.

**Multiple macro fallback fixtures — source at the primary revision.** `tests/elab/extensibleTacticBug.lean`, blob `eeee29bfc11ba20b27da24cbdfe8362d471b856c`, and `tests/elab/evalTacticBug.lean`, blob `24435e9a58a0158d7d64ee36ed6827f99f5da932`. They register multiple macro rules for one tactic syntax kind and rely on fallback/expansion behavior.

**Incremental marker — source at the primary revision.** `src/Lean/Elab/Term.lean`; `isIncrementalElab` recognizes builtin incremental declarations and the ordinary `incremental` attribute, which `evalTactic` consults before exposing tactic snapshots to an elaborator.

## Revalidation

When the Lean pin changes, revalidate this report cheaply in the following order:

1. Confirm the new `Lean.Elab.Tactic.TacticM`, `Tactic`, `Context`, and `State` definitions. A changed monad stack or goal representation changes the extension contract directly.
2. Inspect `tacticElabAttribute` and `mkElabAttribute`. Verify the ordinary/builtin attribute names, serializable keyed-declaration representation, and direct-attribute guidance.
3. Inspect `evalTactic`. Record macro-versus-elaborator precedence, candidate failure classes that trigger fallback, state restoration, selected final error, provenance recording, and incremental gating.
4. Inspect `ElabRules.lean` and `MacroRules.lean`. Verify how `elab`, `elab_rules`, `macro`, and `macro_rules` lower for the `tactic` category and whether priorities or no-fallback controls have been added.
5. Inspect `Parser.Extension`, `Elab.Syntax`, and the tactic category registration. Confirm parser priority, scoped/local/export behavior, `.olean` reconstruction, and tactic category identity.
6. Re-run or inspect equivalent regression fixtures that combine macro and tactic elaborator rules for the same kind and multiple fallback rules for one kind.
7. If Anneal relies on interactive reuse, add a small exact-pin probe with one ordinary custom tactic and one `@[incremental]` custom tactic under Lean server edits. Verify that correctness does not depend on reuse and that cancellation/restart preserves expected diagnostics and goals.
8. If Anneal introduces its own tactic package, add a two-module integration fixture: module A defines/export the tactic syntax and elaborator; module B imports A and uses the tactic in a theorem. Archive the exact generated `.olean`/build identities and verify that a clean rebuild and relocated build both reconstruct the extension without process-local setup.

A change in fallback ordering, parser/elaborator registry representation, incremental exposure, or high-level command lowering should be treated as a material compatibility event for generated Anneal proof scripts.