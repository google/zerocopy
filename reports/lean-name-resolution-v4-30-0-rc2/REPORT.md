# Lean namespace and name resolution at v4.30.0-rc2

## Summary

At `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (`v4.30.0-rc2`), an identifier does not resolve from its spelling alone. Global resolution depends on the current namespace, the ordered `open` declarations in scope, persistent aliases created by `export`, protected/private visibility, macro-scope information, and any pre-resolved declaration metadata carried by the identifier syntax. Term elaboration adds the local context and may keep several global interpretations alive long enough for typing to select one.

The highest-value rule for generated Lean is therefore simple: **the same short identifier can denote a different declaration, become ambiguous, or stop resolving when its namespace/open/local/hygiene context changes**. Fully qualified names reduce that dependence, but `_root_`, private names, macro scopes, projections, and syntax quotations still have specific semantics.

No fresh Lean execution was performed. The report is source- and documentation-based at the exact revision Anneal selects.

## Applicability

- Lean: `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`, release `v4.30.0-rc2`.
- Anneal: `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`; `anneal/flake.nix` sets `leanVersion = "v4.30.0-rc2"`.
- Subject: ordinary Lean declaration/namespace lookup, `open`/`export`, protected names, local-vs-global lookup, and the interaction of name resolution with hygienic syntax.

The report describes this pinned implementation. It does not assume adjacent Lean releases preserve the same lookup order or internal APIs. It also does not claim that Aeneas or Anneal currently emits names in any particular style; the implications for generated proof code are derived from Lean's resolver behavior.

## Findings

### Resolution state is explicit and scoped

Command elaboration carries a `Scope` whose naming state includes `currNamespace` and `openDecls`. A nested `section` or `namespace` starts from a modified copy of its parent scope, so opens and namespace context follow ordinary lexical scope. `CommandElabM` and the lifted core/term elaborators expose that state through `MonadResolveName`.

A `namespace A.B` command extends the current namespace component by component. Each entered namespace is also passed to `activateScoped`, which affects scoped extensions such as scoped notation or instances. That activation is related to, but distinct from, declaration-name lookup.

Basis: **source** (`Lean.Elab.Command.Scope`, `Lean.Elab.Command.addScope`/`addNamespace`).

### Global lookup first prefers the nearest enclosing namespace

`ResolveName.resolveGlobalName` implements the core global lookup. For an identifier `id`, it first calls `resolveUsingNamespace`, which tries `currentNamespace ++ id`, then successively removes enclosing namespace components. **The first namespace prefix that yields any candidate stops this search.** A declaration in a nearer namespace therefore shadows candidates that would have been found from an outer namespace through this phase.

For a non-atomic identifier, if no enclosing-namespace candidate exists, `resolveExact` next tries the exact global spelling. `_root_.X` is implemented by replacing the `_root_` prefix with the anonymous/root namespace before this exact lookup. Atomic identifiers skip this exact-name phase.

If neither phase succeeds, the resolver then considers the spelling itself, accessible private forms, current `open` declarations, and persistent aliases. Duplicate candidate names are removed, but multiple distinct candidates remain multiple interpretations rather than being silently ordered into a winner.

Basis: **source** (`Lean.ResolveName.ResolveName.resolveUsingNamespace`, `resolveExact`, `resolveGlobalName`).

### Dotted spelling may be a qualified name or a projection chain

Global resolution does not assume every dot is part of a declaration's fully qualified name. If a full dotted spelling cannot be resolved, `resolveGlobalName` repeatedly removes its final component and accumulates removed components as potential fields. Thus, with `Foo.x` available, a spelling such as `x.z.w` may resolve to the declaration `Foo.x` plus projection/field components `z`, `w`.

APIs that require a global constant, such as `resolveGlobalConst`, discard candidates whose field list is nonempty. Application/term elaboration uses the richer result and can elaborate the suffix as projections.

This distinction matters for generated code: concatenating textual name components is not equivalent to referring to a declaration identity.

Basis: **source** (`Lean.ResolveName.resolveGlobalName`, `filterFieldList`; `Lean.Elab.App.elabAppFnResolutions`).

### `open` has several materially different forms

The pinned parser documentation and `Lean.Elab.Open.elabOpenDecl` distinguish these cases:

- `open N` adds a simple `OpenDecl` for `N` and activates scoped extensions from `N`.
- `open N hiding x y` adds a simple open with exclusions and also activates scoped extensions.
- `open N (x y)` creates explicit mappings for only those names.
- `open N renaming x → z` creates explicit mappings under the requested new spelling.
- `open scoped N` activates scoped extensions but **does not add ordinary declaration names to `openDecls`**.

Simple opens resolve `N ++ id`. Explicit opens instead map a particular opened spelling to a particular resolved declaration, and prefix replacement allows a longer spelling beginning with that opened identifier to continue beneath the selected declaration name when such a candidate exists.

Because new open declarations are stored in scoped state rather than copied into declaration identities, short-name meaning remains context-dependent.

Basis: **documentation + source** (`Lean.Parser.Command.open`; `Lean.Elab.Open.elabOpenDecl`; `Lean.ResolveName.resolveOpenDecls`).

### Protected declarations are excluded from broad opens, not from explicit access

`resolveQualifiedName` ignores a protected declaration when the queried `id` is atomic. This is the mechanism behind the documented rule that a broad `open N` exposes non-protected names. The same function filters protected alias targets for atomic lookup.

Selective and renaming opens behave differently: `open N (x)` and `open N renaming x → y` first resolve the requested declaration and then install an explicit `OpenDecl`. The parser documentation explicitly states that these forms can expose protected declarations. A qualified non-atomic spelling can also refer to a protected declaration.

`protected` therefore controls unqualified broad lookup; it is not a general access-control boundary.

Basis: **documentation + source** (`Lean.Parser.Command.open`; `Lean.ResolveName.resolveQualifiedName`; `Lean.Elab.Open.elabOpenDecl`; `Lean.Elab.DeclModifiers.applyVisibility`).

### `export` creates persistent aliases in the environment

Lean implements `export A (x)` with the alias environment extension. Inside namespace `B`, `export A (x)` records an alias `B.x → A.x`. Alias state is persistent in the environment and may map one alias spelling to more than one declaration.

The command documentation describes the intended user effect: `x` becomes visible in the current namespace, and users outside that namespace can refer to it as `B.x`. This is stronger and longer-lived than a lexical `open` declaration.

Aliases participate in ordinary global name resolution. For atomic lookup, protected alias targets are filtered in the same way as protected direct names unless an explicit open supplies the mapping.

Basis: **documentation + source** (`Lean.Parser.Command.export`; `Lean.Elab.Command.elabExport`; `Lean.addAlias`/`getAliases`; `Lean.ResolveName.resolveGlobalName`).

### Namespace resolution is related to, but separate from, declaration resolution

`ResolveName.resolveNamespace` searches for namespaces with its own procedure. It first looks through the current namespace from inner to outer and keeps at most the first scoped match; it then adds matches reachable through simple `open` declarations. Explicit name opens do not participate in this namespace search.

This distinction matters to commands such as `open` and `export`, which first resolve namespace identifiers before resolving declarations beneath them. An identifier syntax can also carry a pre-resolved namespace candidate, in which case syntax-aware namespace resolution uses that saved identity rather than repeating ordinary textual lookup.

Basis: **source** (`Lean.ResolveName.resolveNamespaceUsingScope?`, `resolveNamespaceUsingOpenDecls`, `resolveNamespace`).

### Locals shadow globals, and term elaboration can disambiguate overloaded globals by type

Local-name resolution walks the local context from newest to oldest. The source explicitly preserves the rule that a local with the same name shadows a global. Dotted local spellings are also considered together with possible projection suffixes, with special handling for auxiliary declarations created while elaborating recursive or `where` definitions.

Global lookup can return several candidates. Application elaboration evaluates candidate interpretations separately. If exactly one interpretation elaborates successfully, it can be selected; if several remain successful, Lean reports an ambiguous term. Therefore, `open Foo` plus `open Boo` need not cause an immediate name-resolution error for every overloaded function spelling: expected types and application elaboration may eliminate alternatives.

Generated proof code should not rely on that type-directed rescue unless the ambiguity is intentional and stable. A change in expected type or surrounding locals can change which candidate survives.

Basis: **source** (`Lean.resolveLocalName`; `Lean.Elab.App.elabAppFnResolutions`, `getSuccesses`, `elabAppAux`).

### Hygienic syntax can carry declaration identity across a later resolution context

Lean syntax identifiers contain more than a printed `Name`. Syntax quotations with hygiene enabled resolve visible global constants, section variables, and namespaces when the quotation is elaborated and store those results as `Syntax.Preresolved` entries. They also add macro scopes. Later syntax-aware resolution routines first consult the saved pre-resolved declaration or namespace entries; when applicable, they return those identities instead of re-running ordinary open/namespace lookup from the spelling alone.

This creates an important split for generators:

- code emitted as raw text is reparsed and resolved in the destination namespace/open/local context;
- code built through ordinary hygienic quotations can retain pre-resolved declaration identities and macro scopes across expansion.

It follows that a source-to-source generator cannot reason about binding stability from printed text alone. If it serializes syntax to text and reparses it, it discards the pre-resolved identity that hygienic syntax could have carried.

Basis: **source + derived** (`Lean.Elab.Term.Quotation.quoteSyntax`; `Lean.preprocessSyntaxAndResolve`; `Lean.resolveNamespace`).

### Practical rule for Anneal-facing generated Lean

For generated proof or annotation code that should remain stable under surrounding imports and namespace changes:

1. Prefer a declaration identity represented through syntax-aware/hygienic construction where the generation architecture permits it.
2. When emitting plain Lean source, prefer sufficiently qualified global names rather than assuming a convenient `open` environment.
3. Treat `_root_` as an explicit root qualification, not as a generic hygiene mechanism.
4. Do not assume broad `open` exposes protected declarations; use qualified or explicit forms deliberately.
5. Treat locals, expected types, and projection syntax as part of the resolution environment when reproducing an interactive proof state.
6. If a future Anneal LSP/MCP feature asks Lean to interpret user-written annotations, preserve the actual `currNamespace`, `openDecls`, local context, and elaborated syntax context instead of resolving names in a reconstructed global environment.

These are **derived** engineering consequences of the pinned resolver. They are not claims that current Anneal already uses these strategies.

## Boundaries

- **No fresh execution.** No Lean process or language server was run. Examples and behavior are taken from pinned source and source documentation.
- **Parser lexical details not examined.** This report does not catalog Unicode identifier syntax, escaping, tokenization, or parser recovery.
- **Private-name behavior only partially covered.** The resolver's private-name checks were inspected enough to avoid treating private names like ordinary public names, but module-system `import all` and private-name encoding are not independently characterized here.
- **Scoped extensions are not ordinary name lookup.** `open scoped` and namespace entry can activate scoped notation, attributes, or instances; this report records that boundary but does not inventory each scoped extension mechanism.
- **Type-directed dotted notation is broader than this report.** `Lean.Elab.App` has an additional expected-type-driven `.field` path. The report establishes that such behavior exists but does not inventory every projection/method lookup rule.
- **No adjacent-version claim.** The resolver is implementation source, not a promise that future Lean revisions keep the same order or APIs.
- **No Aeneas naming claim.** The report does not establish which names Aeneas emits, how often it qualifies them, or whether its generated source depends on opens. Those are separate Aeneas questions.

## Evidence

All Lean source below is from `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (`v4.30.0-rc2`). Evidence was acquired on 2026-09-26.

- **source** — `src/Lean/ResolveName.lean`, blob `9b3d11ee12bdc1ff3885d6da83cb89e7f3130e0c`: alias storage; `resolveQualifiedName`; namespace search; exact/root lookup; open-declaration lookup; projection fallback; syntax-aware constant/namespace resolution; local-name shadowing; reverse/unresolve helpers.
- **source** — `src/Lean/Elab/Open.lean`, blob `b91c0aca54d99bcda8fb15df81b71347dafc173c`: elaboration of simple, scoped, selective, hiding, and renaming opens.
- **documentation + source** — `src/Lean/Parser/Command.lean`, blob `9b8d6b4eb39a611ffd3b9db0f9d17b1e7f653f70`: user-facing `open` and `export` semantics, including protected names and `open scoped`.
- **source** — `src/Lean/Elab/BuiltinCommand.lean`, blob `c1f80b79afe80c1cfd08f830b9f6d1014c815b1b`: namespace scope construction, `elabExport`, and `elabOpen`.
- **source** — `src/Lean/Elab/Command/Scope.lean`, blob `95898f00d61b57e79060784cfb5e8ed880754299`: scoped `currNamespace` and `openDecls` state.
- **source** — `src/Lean/Elab/DeclModifiers.lean`, blob `5289bd4dccfec6366e9f03a8db2d483ed8941542`: protected declaration registration and declaration-name construction.
- **source** — `src/Lean/Elab/Quotation.lean`, blob `8213946421eefb8d9285f496a3c5b4e57958e223`: hygienic quotation pre-resolution of declarations, section variables, and namespaces.
- **source** — `src/Lean/Elab/App.lean`, blob `3ecd61a814bff650fe60e0b8f7655f25d7eb05be`: elaboration of multiple name interpretations, projection suffixes, expected-type dotted identifiers, and ambiguity handling.
- **source** — `src/Lean/Elab/Command.lean`, blob `1b9bd263858518f56403e3657821edd56fde2f39`: propagation of `currNamespace` and `openDecls` from command scopes into Core/Term elaboration.
- **source** — `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`, `anneal/flake.nix`, blob `433fcf5c64da4f51b9fac471f1faf45c1f730cba`: Anneal selects `leanVersion = "v4.30.0-rc2"`.

No **execution** evidence is used. The high-level guidance for generators is **derived** from the source mechanisms above.

## Revalidation

For a different Lean revision, first diff these narrow implementation surfaces rather than repeating broad research:

1. `src/Lean/ResolveName.lean`: `resolveQualifiedName`, `resolveUsingNamespace`, `resolveExact`, `resolveOpenDecls`, `resolveGlobalName`, `resolveNamespace`, `resolveLocalName`, and syntax-aware pre-resolution helpers.
2. `src/Lean/Elab/Open.lean`: `elabOpenDecl` and explicit-open construction.
3. `src/Lean/Elab/BuiltinCommand.lean`: namespace scope creation, `elabExport`, and `elabOpen`.
4. `src/Lean/Elab/Quotation.lean`: identifier handling in `quoteSyntax`.
5. `src/Lean/Elab/App.lean`: multi-candidate elaboration and dotted/projection handling.

A capable execution surface can cheaply confirm the user-visible boundary with one small Lean file containing: nested namespaces with the same short name, two broad opens producing an overload, a protected declaration tested under broad versus selective open, an `export`, a local shadowing a global, `_root_` qualification, and a hygienic macro quotation expanded under a conflicting open. Record exact stdout/diagnostics and the Lean revision. That probe would validate the principal observable consequences but would not replace source inspection for hidden ordering or macro metadata semantics.