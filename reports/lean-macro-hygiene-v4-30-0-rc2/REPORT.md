# Lean macro hygiene at v4.30.0-rc2

## Summary

At `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (`v4.30.0-rc2`), ordinary syntax quotation protects generated code from two different capture hazards.

First, identifiers written directly inside a quotation receive a macro scope. Lean gives each macro invocation a fresh numeric scope and combines it with a globally unique quotation context. A binder introduced by one expansion therefore does not accidentally capture same-spelled syntax from the call site, and independently expanded helpers do not collide merely because they use the same textual name.

Second, quotation pre-resolves possible global declarations, section variables, and namespaces at the quotation's definition site. Later global name resolution honors those saved candidates instead of silently retargeting the identifier to a newly visible same-spelled declaration at the macro's use site.

Antiquotations follow the opposite rule: the inserted syntax is carried through as-is. That preserves the caller's scopes and pre-resolution metadata instead of reclassifying caller syntax as macro-introduced syntax.

These guarantees depend on using the hygienic quotation machinery. The `hygiene` quotation option defaults to `true`, but it can be disabled. Code that constructs `Syntax` directly, erases macro scopes, or otherwise bypasses quotation must preserve the intended binding behavior itself. Macro hygiene is a frontend name-resolution property; it does not establish kernel soundness, Rust-to-Lean semantic adequacy, or correctness of a custom elaborator.

No fresh Lean execution was performed.

## Applicability

- Lean: `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`, tag `v4.30.0-rc2`.
- Anneal: `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`; `anneal/flake.nix` sets `leanVersion = "v4.30.0-rc2"`.
- This report concerns Lean's macro-expansion and syntax-quotation hygiene. It does not treat `tactic.hygienic` as the same mechanism; that option governs accessibility of tactic-generated local names and has a different purpose.
- The conclusions apply to syntax produced through the pinned quotation machinery while its `hygiene` option is enabled. Custom syntax constructors and elaborators require separate review if they bypass that machinery.

The report uses pinned source as the authority for this release. The Lean reference manual and the Ullrich–de Moura macro-hygiene paper are explanatory background where noted.

## Findings

### Quotation adds both local hygiene and global-reference stability

`Lean.Elab.Term.Quotation.quoteSyntax` handles an identifier in two stages when quotation hygiene is enabled.

It first resolves possible global declarations, section variables, and namespaces at quotation elaboration time and stores them in the identifier's `Syntax.Preresolved` list. It then emits code that calls `addMacroScope quotCtx val scp` when the quotation runs. The source describes these as “global scopes at compilation time” and a “macro scope at runtime.”

That division blocks two distinct capture modes:

1. **Local capture.** Macro-introduced binders and their macro-introduced uses carry the same fresh macro scope. Call-site syntax does not gain that scope, so an introduced same-spelled binder does not accidentally capture it.
2. **Global retargeting.** A literal global identifier in the macro body carries the declarations or namespaces that were in scope where the quotation was defined. `resolveGlobalConst` uses those pre-resolved candidates when present rather than re-running ordinary ambient resolution and accepting a different later declaration.

Basis: **source** + **derived**.

### Antiquotations preserve caller identity

The quotation implementation explicitly inserts a non-escaped antiquotation's syntax “as-is.” It does not apply the current quotation macro scope to that inserted subtree.

This is the complementary half of hygiene. Syntax supplied by the caller retains the scopes and pre-resolution metadata it already had. A macro can therefore introduce a binder named `x` without making an antiquoted caller expression that happens to mention textual `x` refer to the new binder.

Basis: **source** + **derived**.

### A hygienic name carries context plus a stack of macro scopes

The pinned `Init.Prelude` encodes hygienic names with an original name, a quotation context, and macro-scope numbers. `MacroScopesView` separates these components and can reconstruct the encoded `Name`.

The context exists because numeric scope counters restart across files. The implementation further makes the context unique per declaration so unrelated elaboration does not perturb exported hygienic names. The source records two reasons: more stable native-symbol lookup and fewer unnecessary module rebuilds.

Scopes can accumulate when syntax crosses quotation contexts, including macros defined in imported files and expanded in the current file. `addMacroScope` preserves an existing scope chain and appends or rehomes it under the new context rather than discarding it.

Basis: **source**.

### Every macro call can establish a fresh scope

`MonadQuotation.withFreshMacroScope` is the abstraction for beginning a new macro-invocation context. Its documentation says callers should use it where work morally begins a new macro call, and it may also be used inside recursive macro implementations when independently introduced identifiers must not collide.

`MacroM` carries a global scope counter in its state. `Macro.withFreshMacroScope` takes the next counter value, increments the state, and runs its body with that value as `currMacroScope`. `CoreM.State` separately documents that the next macro scope exists “to avoid accidental name capture.”

This means freshness is attached to expansion structure, not to a textual gensym convention chosen by each macro author.

Basis: **source**.

### Name resolution consumes hygiene metadata instead of stripping it away

Local resolution extracts the macro-scope view and, for ordinary local declarations, requires exact equality between the local declaration's `userName` and the scoped name being resolved. Same textual spelling without the same hygienic name is therefore insufficient.

Global resolution likewise decodes macro scopes rather than treating the encoded name as ordinary text. For identifiers represented as `Syntax`, `preprocessSyntaxAndResolve` checks `Syntax.Preresolved`; if declaration candidates were saved by quotation, it returns them directly instead of consulting ordinary global resolution.

The implementation does erase macro scopes in places where the program intentionally wants textual identity rather than binding identity—for example some syntax-pattern comparisons. That is an explicit operation, not the default name-resolution rule.

Basis: **source** + **derived**.

### The automatic guarantee has explicit escape hatches

At this revision, the quotation option `hygiene` defaults to `true`. Its source description says it annotates identifiers so they resolve relative to their declaration scope rather than their eventual expansion scope. When the option is false, `quoteSyntax` emits the original identifier value and pre-resolution data without adding the usual quotation-time hygiene metadata.

Lean also exposes `Name.eraseMacroScopes`, `Macro.addMacroScope`, and lower-level `Syntax` constructors. These are necessary for implementation work, but they mean “Lean macros are hygienic” is not a theorem about arbitrary syntax-producing metaprograms. A macro or elaborator that constructs identifier syntax manually must preserve the desired scopes and global-reference information itself.

`Lean.Unhygienic` makes this boundary explicit. Its documentation says it does not guarantee globally fresh names across independent runs and is safe only under additional restrictions, such as not introducing bindings around antiquotations and using `_root_.` for global references.

Basis: **source** + **documentation**.

### Auto-bound implicits show why hygienic names must remain semantically distinct

`Lean.Elab.AutoBound` preserves a historical failure mode that is useful for understanding the contract. An earlier implementation erased macro scopes when deciding whether an unknown identifier could become an auto-bound implicit. A notation that generated `x` with a fresh scope could then repeatedly create distinct scoped `x` names, causing an expansion loop. The pinned source now rejects scoped identifiers as auto-bound implicit candidates.

The lesson is narrower than “never erase scopes.” It is that a subsystem must decide deliberately whether it is comparing textual spelling or binding identity. Erasing scopes before a binding-sensitive decision can change semantics.

Basis: **source** + **derived**.

### Implication for Anneal-generated Lean

For future Anneal annotations or proof-generating macros, ordinary Lean quotations provide a strong default: helper binders introduced by the macro are isolated from caller syntax, while literal global references in the macro body are pinned to the definition-site candidates that quotation recorded.

That protection disappears at boundaries that deliberately bypass quotation hygiene. Any Anneal component that emits raw `Syntax`, calls `eraseMacroScopes`, disables quotation hygiene, or implements custom elaboration with its own identifier construction should treat name-binding preservation as an explicit proof obligation.

This matters for source correspondence and proof generation, but it is not itself part of Lean's trusted kernel. If a macro expands to a well-typed term proving a theorem, the kernel checks that term under Lean's normal rules; macro hygiene instead controls which names the frontend selects while constructing and elaborating the term.

Basis: **source** + **derived**.

## Boundaries

- **No fresh execution.** This report did not run macro examples under the pinned toolchain. It reconstructs behavior from exact source and upstream documentation.
- **Not every metaprogramming API was inventoried.** The report covers the core quotation, macro-scope representation, `MacroM`, and name-resolution path. It does not claim that every custom elaborator or syntax helper automatically preserves hygiene.
- **`tactic.hygienic` is separate.** Tactic-generated inaccessible names are related to capture avoidance but are not the macro-quotation mechanism described here.
- **No adjacent-version continuity claim.** Lean's hygiene representation and frontend implementation can change even when ordinary macro behavior remains source-compatible.
- **No logical-soundness claim.** Hygiene prevents accidental identifier capture. It does not prove that a macro implements the intended transformation, that generated Lean corresponds to Rust, or that the Lean kernel/compiler/runtime is correct.
- **Manual scope erasure is not inherently a bug.** Several Lean subsystems intentionally erase scopes when comparing syntax as syntax. The risk arises when a caller erases scopes where binding identity is semantically relevant.

## Evidence

### Exact pinned source

All source observations below use `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`.

- **source** — `src/Init/Prelude.lean`, blob `e55fd8785ca9d4f4b7ea61ce5c6939628d4bfe4b`
  - `MonadQuotation` and `withFreshMacroScope`, lines 5525–5545.
  - Note `Macro Scope Representation`, lines 5558–5591.
  - `MacroScopesView`, `extractMacroScopes`, and `addMacroScope`, lines 5625–5710.
  - `MacroM.State`, `Macro.withFreshMacroScope`, and its `MonadQuotation` instance, lines 5798–5882.
- **source** — `src/Lean/Elab/Quotation/Util.lean`, blob `379e6e6a2d3cd1ddf02db0e3dc98b56534cff7a0`
  - quotation option `hygiene`, default `true`, lines 13–17.
- **source** — `src/Lean/Elab/Quotation.lean`, blob `8213946421eefb8d9285f496a3c5b4e57958e223`
  - `quoteSyntax` identifier handling and antiquotation passthrough, lines 125–153.
  - bootstrap-hygiene note, lines 243–255.
- **source** — `src/Lean/ResolveName.lean`, blob `9b3d11ee12bdc1ff3885d6da83cb89e7f3130e0c`
  - pre-resolved global handling, lines 382–405.
  - scoped local-name resolution, lines 459–568.
- **source** — `src/Lean/CoreM.lean`, blob `3403cbfde65a41ea67336b83007ff4d4b5b8f3ca`
  - `nextMacroScope` and its capture-avoidance purpose, lines 184–190.
- **source** — `src/Lean/Hygiene.lean`, blob `fba62a5b700d9d22fd11e2f8726fe4d85bf5b754`
  - `Unhygienic` limitations and scope allocation, lines 16–44.
- **source** — `src/Lean/Elab/AutoBound.lean`, blob `8a012c47a2412c01bf1f5994ef393a3df17cbbd6`
  - issue #255 explanation of scope erasure and auto-bound implicit loops, lines 38–49.

Anneal applicability uses `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`, `anneal/flake.nix`, blob `433fcf5c64da4f51b9fac471f1faf45c1f730cba`, where line 43 selects `v4.30.0-rc2`.

### Upstream explanatory material

- **documentation** — Lean reference manual, “Macros”, §23.5.1 “Hygiene”, observed 2026-09-26. It describes macro scopes, pre-resolved identifiers, quotation as the automatic-hygiene boundary, and the need for manually constructed syntax to supply its own hygiene.
- **documentation** — Sebastian Ullrich and Leonardo de Moura, *Beyond Notations: Hygienic Macro Expansion for Theorem Proving Languages*, 2020, arXiv:2001.10490. The pinned quotation source explicitly points readers to this paper for the algorithmic background.

No **execution** evidence was acquired.

## Revalidation

For another Lean revision, start with the narrow source surface rather than rerunning broad research:

1. Diff `src/Init/Prelude.lean` around `MonadQuotation`, `MacroScopesView`, `addMacroScope`, and `Macro.withFreshMacroScope`.
2. Diff `src/Lean/Elab/Quotation/Util.lean` for the `hygiene` option and `src/Lean/Elab/Quotation.lean` for identifier and antiquotation handling.
3. Diff `src/Lean/ResolveName.lean` for pre-resolved-global and local scoped-name resolution.
4. If those mechanisms changed materially, repeat the binding analysis before generalizing this report.

A small execution probe can then distinguish the important behavior:

- define a macro that introduces `let x := ...` around an antiquoted caller term containing its own `x`, and verify the caller's `x` is not captured;
- define a macro whose quotation contains a literal global `f`, introduce a different same-spelled `f` at the use site, and verify the expansion retains the definition-site target;
- invoke the same recursive/helper-producing macro multiple times and verify its generated binders remain independent;
- repeat with `set_option hygiene false` or deliberately constructed raw identifier syntax to confirm the boundary rather than assuming automatic hygiene there.

Passing those probes would validate the selected capture cases only. It would not establish correctness for arbitrary custom elaborators or raw syntax construction.