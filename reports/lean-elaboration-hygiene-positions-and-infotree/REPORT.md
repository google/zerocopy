# Lean 4 Namespace Resolution, Macro Hygiene, Source Positions, InfoTree, and Pretty-Printing

## Summary

Across Lean 4 `v4.29.0` (`leanprover/lean4@98dc76e3c0a9b856c9b98726b713fb04fab16740`), `v4.30.0-rc2` (`leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`), and `v4.34.1` (`leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`), frontend elaboration state, macro hygiene, source positions, elaboration `InfoTree` metadata, and pretty-printing form five distinct layers that generated-code and interactive-verification tools must keep separate from both raw source text and the compiled kernel environment:

1. **Scoped Namespace and Name Resolution (`ResolveName.resolveGlobalName`)**: An identifier does not resolve from its printed spelling alone. Command elaboration carries a lexical `Scope` containing `currNamespace` and `openDecls` (`MonadResolveName`). Global lookup first searches enclosing namespaces from inner to outer (`resolveUsingNamespace`), **stopping at the first namespace prefix that yields any candidate**. Only if no enclosing-namespace candidate exists does a non-atomic identifier try `resolveExact` (with `_root_.X` stripping `_root_` to the anonymous root namespace), followed by raw spelling, accessible private forms, `open` declarations (`resolveOpenDecls`), and persistent `export` aliases (`addAlias` / `getAliases`). Dotted spellings can resolve to a global or local declaration plus a projection/field chain (`filterFieldList`), local variables shadow globals (`resolveLocalName`), and application elaboration (`elabAppFnResolutions`) can keep multiple overloaded candidates alive until typing selects one.
2. **Quotation Macro Hygiene and Capture Avoidance (`quoteSyntax`, `MacroScopesView`)**: With `hygiene` enabled (default `true`), syntax quotations protect generated code against two capture modes: (a) **compile-time pre-resolution**, which resolves visible global constants, section variables, and namespaces at quotation definition time into `Syntax.Preresolved` entries so later resolution (`preprocessSyntaxAndResolve`) does not retarget them at the call site; and (b) **runtime macro scopes** (`addMacroScope quotCtx val scp` via `MonadQuotation.withFreshMacroScope`), which tag macro-introduced binders and uses with a declaration-unique quotation context plus fresh numeric scope so they cannot capture call-site identifiers or collide across recursive expansions. Antiquotations (`$e`) splice caller syntax as-is without applying the macro's fresh scope. Escape hatches (`set_option hygiene false`, `Name.eraseMacroScopes`, `Lean.Unhygienic`, raw `Syntax` constructors) bypass automatic hygiene and require explicit binding preservation.
3. **Parser and Elaborator Source Positions (`String.Pos.Raw`, `SourceInfo`, `FileMap`)**: Raw parser positions (`String.Pos.Raw`) are UTF-8 byte offsets (`byteIdx`, advancing by `Char.utf8Size` / `String.utf8ByteSize`), converted to 1-based line and 0-based Unicode scalar character column by `FileMap.toPosition`. Parsed tokens and identifiers carry `SourceInfo.original leading pos trailing endPos`, whereas ordinary composite `Syntax.node` values and `Syntax.missing` carry `SourceInfo.none` and derive ranges from leftmost/rightmost positioned descendants (`getPos?`, `getTailPos?`, `getRange?`). Generated syntax carries `SourceInfo.synthetic pos endPos canonical` (`SourceInfo.fromRef`), where `canonical = true` marks synthetic spans eligible for `canonicalOnly := true` hover/diagnostic queries without claiming literal source-text identity. The elaborator treats syntax as an error-reporting reference (`MonadRef`): `withRef` / `replaceRef` refuses to overwrite a positioned reference with positionless syntax, and `Lean.logAt` falls back from a positionless requested reference to `← getRef` and then offset `0`.
4. **Elaboration `InfoTree` and Artifact Persistence (`Lean.Elab.InfoTree`)**: `InfoTree` is a context-sensitive elaboration tree (`context PartialContextInfo InfoTree`, `node Info (PersistentArray InfoTree)`, `hole MVarId`) attached to asynchronous language-processing snapshots (`Snapshot.infoTree?` / `Snapshot.infoTree`). It preserves local contexts, metavariable contexts, elaborated expressions, expected types (`TermInfo`, `PartialTermInfo`), before/after tactic goals (`TacticInfo` with `mctxBefore`, `goalsBefore`, `mctxAfter`, `goalsAfter`), macro expansions (`MacroExpansionInfo`), completions, and dynamic widgets (`CustomInfo`), allowing `ContextInfo.runMetaM` to re-enter `MetaM` retroactively. Server queries (`Lean.Server.InfoUtils.smallestInfo?`, hover, goal lookup) apply explicit span-selection heuristics over potentially overlapping sibling ranges. Ordinary `.olean` serialization (`writeModule`) does **not** persist `InfoTree`; `.ilean` generation (`Lean.Server.findModuleRefs`) writes only a reduced JSON reference/declaration index.
5. **Pretty-Printing and Semantic Round Trips (`ppCategory`, `ppExpr`, `Delaborator`)**: Pretty-printed text is regenerated surface syntax, not a byte-stable serialization of either source text or kernel `Expr` values. `ppCategory` (`ppTerm`, `ppTactic`, `ppCommand`) runs `sanitizeSyntax` (which can erase macro scopes via `sanitizeName` into inaccessible names) $\rightarrow$ `parenthesizeCategory` $\rightarrow$ `formatCategory`, normalizing layout, whitespace, and Unicode/ASCII token spellings (`pp.unicode`, `pp.unicode.fun`, `preserveForPP`). `ppExpr` first delaborates kernel expressions (`Delaborator.delab` / `delabCore`) under `pp.*` options (`pp.explicit`, `pp.universes`, `pp.fullNames`, `pp.notation`, `pp.proofs`, `pp.maxSteps`), optionally instantiating metavariables, beta-reducing, or eliding proofs as `⋯`. Lean's checked-in `tests/elab/PPRoundtrip.lean` (`checkM`) defines round-trip adequacy semantically—elaborate $\rightarrow$ delaborate $\rightarrow$ `ppTerm` $\rightarrow$ `runParserCategory` $\rightarrow$ elaborate $\rightarrow$ `isDefEq e e'`—and documents known non-round-tripping cases for metavariables and universe metavariables.

## Applicability

### Covered Versions and Subjects

| Subject | Repository | Revision | Version / Scope |
| :--- | :--- | :--- | :--- |
| Lean 4 prior baseline | `leanprover/lean4` | `98dc76e3c0a9b856c9b98726b713fb04fab16740` | `v4.29.0` |
| Lean 4 baseline selected by Anneal | `leanprover/lean4` | `3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` | `v4.30.0-rc2` |
| Lean 4 newer revalidation target | `leanprover/lean4` | `5045d0056413266e57c625dcd7c365b10e377c52` | `v4.34.1` |
| Anneal toolchain configuration | `google/zerocopy` | `41f5b37afe7060fd9fe08c00b200672cd76d77b9` | `anneal/flake.nix` (blob `433fcf5c64da4f51b9fac471f1faf45c1f730cba`, line 43 `leanVersion = "v4.30.0-rc2"`) |

### Scope and Persistence Definitions

- This package covers ordinary Lean declaration/namespace lookup (`open`, `export`, `protected`, local vs. global shadowing, dotted projections), macro-quotation hygiene (`Syntax.Preresolved`, `MacroScopesView`, `MonadQuotation`), parser and elaborator `SourceInfo` / `String.Pos.Raw` / `FileMap` coordinates, `Lean.Elab.InfoTree` representation and `.olean`/`.ilean` persistence boundaries, and `Lean.PrettyPrinter` / `Delaborator` round-trip semantics.
- `tactic.hygienic` is separate from macro-quotation hygiene: `tactic.hygienic` governs accessibility of tactic-generated local names rather than syntax-quotation macro scopes.
- "Persisted" with respect to `InfoTree` means serialized into an on-disk build artifact (`.olean` or `.ilean`) that survives after the elaborating process and its in-memory snapshots terminate.

## Findings

### 1. Scoped Namespace and Name Resolution (`Lean.ResolveName`)

#### Explicit Lexical Scope (`currNamespace` and `openDecls`)

Command elaboration carries a `Command.Scope` (`src/Lean/Elab/Command/Scope.lean`, blob `95898f00d61b57e79060784cfb5e8ed880754299`) whose naming state includes `currNamespace` and `openDecls`. Entering a nested `section` or `namespace` copies and modifies the parent scope, and `CommandElabM` propagates `currNamespace` and `openDecls` into Core and Term elaboration through `MonadResolveName` (`src/Lean/Elab/Command.lean`, blob `1b9bd263858518f56403e3657821edd56fde2f39`; `src/Lean/Elab/BuiltinCommand.lean`, blob `c1f80b79afe80c1cfd08f830b9f6d1014c815b1b`). A `namespace A.B` command extends `currNamespace` component by component and passes each entered namespace to `activateScoped` (activating scoped notation, attributes, or instances—a mechanism distinct from ordinary declaration-name lookup).

#### Enclosing-Namespace Priority, `_root_`, Opens, and Aliases

`ResolveName.resolveGlobalName` (`src/Lean/ResolveName.lean`, blob `9b3d11ee12bdc1ff3885d6da83cb89e7f3130e0c` in `v4.30.0-rc2`; 701 lines, SHA-256 `29568f90bc8c5b71...`, `resolveGlobalName` at line 194 in `v4.34.1`) resolves an identifier `id` in ordered phases:

1. **Enclosing namespace search (`resolveUsingNamespace`)**: Tries `currNamespace ++ id`, then successively strips enclosing namespace components from inner to outer. **The first namespace prefix that yields any candidate terminates this phase.** A declaration in a nearer enclosing namespace therefore shadows candidates in outer namespaces during `resolveUsingNamespace`.
2. **Exact global lookup (`resolveExact`)**: For a non-atomic identifier when `resolveUsingNamespace` yields no match, tries the exact global spelling. `_root_.X` is implemented by replacing the `_root_` prefix with `Name.anonymous` before `resolveExact`. Atomic identifiers skip `resolveExact`.
3. **Ambient and open-declaration lookup**: If neither earlier phase succeeds, the resolver checks the raw spelling, accessible private forms, active `open` declarations (`resolveOpenDecls`), and persistent environment aliases (`getAliases`). Duplicate candidate names are deduplicated, but multiple distinct declarations remain multiple candidates rather than being silently ordered into a single winner.

#### Dotted Spellings vs. Field Projections

When a dotted spelling `x.z.w` does not resolve as a full declaration name, `resolveGlobalName` repeatedly strips final dot components and accumulates them as candidate projection fields (`filterFieldList`). With `Foo.x` in scope, `x.z.w` can resolve to the pair `(Foo.x, ["z", "w"])`. Constant-only callers such as `resolveGlobalConst` discard candidates with non-empty field lists, whereas application elaboration (`Lean.Elab.App.elabAppFnResolutions` in `src/Lean/Elab/App.lean`, blob `3ecd61a814bff650fe60e0b8f7655f25d7eb05be`) elaborates non-empty field lists as structure projections or generalized field notation.

#### `open`, `protected`, `export`, and Namespace Lookup

| Construct / Mechanism | Implementation Surface | Resolution Behavior |
| :--- | :--- | :--- |
| `open N` | `Lean.Elab.Open.elabOpenDecl` (`src/Lean/Elab/Open.lean`, blob `b91c0aca54d99bcda8fb15df81b71347dafc173c`) | Installs a simple `OpenDecl` resolving `N ++ id` and activates scoped extensions in `N`. |
| `open N hiding x y` | `elabOpenDecl` | Installs a simple `OpenDecl` excluding `x`, `y` and activates scoped extensions in `N`. |
| `open N (x y)` | `elabOpenDecl` | Resolves `N.x`, `N.y` immediately and installs explicit `OpenDecl` mappings (including prefix replacement for longer spellings below `x` or `y`). |
| `open N renaming x → z` | `elabOpenDecl` | Resolves `N.x` and installs an explicit `OpenDecl` under spelling `z`. |
| `open scoped N` | `elabOpenDecl` (`src/Lean/Parser/Command.lean`, blob `9b8d6b4eb39a611ffd3b9db0f9d17b1e7f653f70`) | Activates scoped extensions in `N` only; **adds no declaration names to `openDecls`**. |
| `protected` declarations | `resolveQualifiedName` (`src/Lean/ResolveName.lean`), `applyVisibility` (`src/Lean/Elab/DeclModifiers.lean`, blob `5289bd4dccfec6366e9f03a8db2d483ed8941542`) | Filtered out when queried via an atomic `id` (including broad `open N` and atomic alias lookup), but exposed via qualified non-atomic spellings, `open N (x)`, and `open N renaming x → y`. |
| `export A (x)` in `namespace B` | `elabExport` (`src/Lean/Elab/BuiltinCommand.lean`), `Lean.addAlias` / `getAliases` | Records a persistent environment alias `B.x → A.x` visible inside `B` as `x` and outside `B` as `B.x` (subject to the same `protected` filter on atomic lookups). |
| Namespace lookup | `resolveNamespaceUsingScope?`, `resolveNamespaceUsingOpenDecls`, `resolveNamespace` | Searches `currNamespace` inner-to-outer (keeping at most the first scoped match) plus simple `OpenDecl` entries; explicit name opens do not participate, and pre-resolved namespace metadata on syntax takes precedence. |
| Local shadowing & overload disambiguation | `Lean.resolveLocalName`, `elabAppFnResolutions`, `getSuccesses`, `elabAppAux` | Walks `LocalContext` newest-to-oldest so locals shadow globals (with projection suffixes and recursive/`where` auxiliary handling). Multiple global candidates are elaborated separately; if exactly one typechecks, it is selected, whereas multiple successes raise an ambiguity error. |

### 2. Macro Hygiene and Capture Avoidance (`Lean.Elab.Quotation`, `Lean.Hygiene`)

#### Two-Stage Hygienic Quotation (`quoteSyntax`)

When the built-in option `hygiene` is `true` (`register_builtin_option hygiene : Bool := true` in `src/Lean/Elab/Quotation/Util.lean`, blob `379e6e6a2d3cd1ddf02db0e3dc98b56534cff7a0`, lines 13–17), `Lean.Elab.Term.Quotation.quoteSyntax` (`src/Lean/Elab/Quotation.lean`, blob `8213946421eefb8d9285f496a3c5b4e57958e223`, lines 125–153 and 243–255) protects identifiers inside syntax quotations in two stages:

1. **Compile-time global pre-resolution**: At quotation elaboration time, Lean resolves visible global declarations, section variables, and namespaces for the quoted identifier and stores the candidates in `Syntax.Preresolved`. During later expansion, `preprocessSyntaxAndResolve` (`src/Lean/ResolveName.lean`, lines 382–405) returns those pre-resolved candidates rather than re-running ambient lookup at the expansion site.
2. **Runtime macro-scope tagging**: At macro expansion time, the quotation emits `addMacroScope quotCtx val scp` (`src/Init/Prelude.lean`, blob `e55fd8785ca9d4f4b7ea61ce5c6939628d4bfe4b`, lines 5525–5882). Each macro invocation acquires a fresh numeric scope via `MonadQuotation.withFreshMacroScope` (`Macro.withFreshMacroScope` in `MacroM.State`, or `nextMacroScope` in `src/Lean/CoreM.lean`, blob `3403cbfde65a41ea67336b83007ff4d4b5b8f3ca`, lines 184–190) combined with a per-declaration unique quotation context `quotCtx` (preventing cross-file counter collisions and avoiding unnecessary native-symbol or module rebuild churn). `MacroScopesView` and `extractMacroScopes` preserve and stack scope chains across imported macros, and scoped local lookup (`src/Lean/ResolveName.lean`, lines 459–568) requires exact equality of the full scoped `userName`.

By contrast, non-escaped antiquotations (`$e`) splice the caller's syntax subtree **as-is** without applying the macro's fresh scope, preserving the caller's own scopes and `Syntax.Preresolved` metadata.

#### Hygiene Escape Hatches and Auto-Bound Implicit Loop Prevention

- Setting `set_option hygiene false`, using `Lean.Unhygienic` (`src/Lean/Hygiene.lean`, blob `fba62a5b700d9d22fd11e2f8726fe4d85bf5b754`, lines 16–44 in `v4.30.0-rc2`; 116 lines, SHA-256 `1f4304254fb225c4...`, `eraseMacroScopes` at line 95 in `v4.34.1`), calling `Name.eraseMacroScopes`, or constructing raw `Syntax` identifiers directly bypasses automatic quotation hygiene.
- `Lean.Elab.AutoBound` (`src/Lean/Elab/AutoBound.lean`, blob `8a012c47a2412c01bf1f5994ef393a3df17cbbd6`, lines 38–49) documents why subsystems must not blindly erase macro scopes before binding-sensitive decisions: an earlier implementation erased macro scopes when checking auto-bound implicits, causing notations that introduced a scoped identifier `x` to loop indefinitely by binding fresh scoped `x` variables on each expansion. The implementation now rejects macro-scoped identifiers as auto-bound implicit candidates.

### 3. Parser and Elaborator Source Positions (`SourceInfo`, `String.Pos.Raw`, `FileMap`)

#### UTF-8 Byte Offsets vs. `FileMap` Line/Column Coordinates

Parser state (`ParserState.pos` in `src/Lean/Parser/Types.lean`, blob `84e5c1fc4dc9dea0506b83d22dfe318f1c692d14`), token caches, and syntax ranges represent positions as `String.Pos.Raw` (`src/Init/Data/String/PosRaw.lean`, blob `505515150dd2e7242b3de08801aa1e660a22f7d3`), which indexes raw UTF-8 bytes (`byteIdx`, advancing by `Char.utf8Size` and `String.utf8ByteSize`). `FileMap.toPosition` (`src/Lean/Data/Position.lean`, blob `f5eae212ed37f753a495437dc7b0c7f6cfeaa945`) converts a raw byte offset to a Lean `Position` by binary-searching precomputed newline byte offsets (1-based line) and decoding UTF-8 characters from the line start to count Unicode scalar values (0-based character column).

#### `SourceInfo` Variants, Parser Error Anchoring, and Elaborator `MonadRef` Fallback

| Mechanism | Source Location (`v4.30.0-rc2` & `v4.34.1`) | Position & Diagnostic Semantics |
| :--- | :--- | :--- |
| `SourceInfo.original leading pos trailing endPos` | `src/Init/Prelude.lean` (`e55fd878...`), `src/Lean/Parser/Basic.lean` (`5b38ff62d8089cb3cebbbf3a70f1fc01b34d98ce`: `mkNodeToken`, `mkTokenAndFixPos`, `mkIdResult`) | Attached to parsed atoms and identifiers with exact UTF-8 start/end byte offsets and surrounding whitespace substrings. |
| `SourceInfo.none` and composite `Syntax.node` ranges | `src/Lean/Parser/Types.lean` (`84e5c1fc...`: `ParserState.mkNode`, `mkTrailingNode`), `src/Lean/Syntax.lean` (`186ff6f39bc50b00793c7c2884ce7c087d29e1ce`) | Ordinary composite parser nodes and recovery `Syntax.missing` carry `SourceInfo.none`. `Syntax.getPos?`, `getTailPos?`, and `getRange?` derive composite spans from the leftmost and rightmost positioned descendants. |
| `SourceInfo.synthetic pos endPos canonical` | `src/Init/Prelude.lean` (`SourceInfo.fromRef`), `src/Lean/Syntax.lean` | Associates macro- or elaborator-generated syntax with a reference span. When `canonical = true`, the synthetic span is visible to `canonicalOnly := true` queries (such as hovers and errors) even though the synthetic token does not literally appear in source text. |
| Parser error ranges (`Parser.Module.mkErrorMessage`) | `src/Lean/Parser/Module.lean` (`024a5c10df494caccca4bb908e7bcc32df2530ca`) | Uses `unexpectedTk` start/end when present—moving the start backward across preceding trailing whitespace to cover token insertion repair points—or produces an empty range at `ParserState.pos` when `unexpectedTk` is absent. |
| Elaborator reference inheritance (`withRef`, `replaceRef`, `logAt`) | `src/Init/Prelude.lean`, `src/Lean/Log.lean` (`3d40ada008ff57e9c82568661f3c4ecf928f9280`) | `replaceRef` keeps the previous positioned reference when the new syntax has no position. `Lean.logAt` applies `replaceRef ref (← getRef)`, takes `pos := ref.getPos?.getD 0` and `endPos := ref.getTailPos?.getD pos`, and converts through `FileMap`. |

### 4. `InfoTree` Elaboration Metadata and Artifact Persistence

#### Structural Representation and `MetaM` Context Recovery

In `src/Lean/Elab/InfoTree/Types.lean` (blob `fdd5cf8581192220ef44328c757ee3f3daa2e781`) and `src/Lean/Elab/InfoTree/Main.lean` (blob `7091272391123485ee731b6eedb528324ef515fe`; re-exported by `src/Lean/Elab/InfoTree.lean`, blob `2bd30aea830988c19fc51176c45c2498cb96c787`), `InfoTree` is defined as:

```text
InfoTree
  = context PartialContextInfo InfoTree
  | node Info (PersistentArray InfoTree)
  | hole MVarId
```

- **Context nodes (`PartialContextInfo`, `CommandContextInfo`, `ContextInfo`)**: `CommandContextInfo` captures `env`, optional final command environment, `fileMap`, `mctx`, `options`, `currNamespace`, `openDecls`, and `ngen`. Nested `PartialContextInfo` nodes refine parent-declaration or auto-implicit state under `mergeIntoOuter?`. `ContextInfo.runMetaM` / `runCoreM` reconstructs a thunked elaboration state so server queries can typecheck, pretty-print, or resolve symbols retroactively.
- **Information nodes (`Info`)**: Includes `TacticInfo` (`mctxBefore`, `goalsBefore`, `mctxAfter`, `goalsAfter`), `TermInfo`, `PartialTermInfo` (retained when term elaboration fails so inner subtrees stay interactive), `CommandInfo`, `MacroExpansionInfo` (source and expanded syntax), `CompletionInfo`, `OptionInfo`, `ErrorNameInfo`, `FieldInfo`, `UserWidgetInfo`, `CustomInfo` (`Dynamic` extension payload), `FVarAliasInfo`, `FieldRedeclInfo`, `DelabTermInfo`, `ChoiceInfo` (retaining failed overload branches when all alternatives fail), `DocInfo`, and `DocElabInfo`.
- **Holes (`hole MVarId`) and lazy substitution**: Postponed elaboration records holes filled via `InfoState.assignment` (`InfoTree.substitute`) or asynchronous `InfoState.lazyAssignment` tasks (`InfoState.substituteLazy`), which command finalization (`src/Lean/Language/Lean.lean`, blob `124d4739bc910eb30ec35844348c785bf9f6c70a`) awaits before storing the tree on the finished snapshot (`src/Lean/Language/Basic.lean`, blob `08f9b688fc869224c316175220403c2aeb5eb415`; `Snapshot.infoTree` at `src/Lean/Server/Snapshots.lean` line 44 in `v4.34.1`).
- **Position selection and `.olean`/`.ilean` persistence**: Because sibling `InfoTree` nodes can have overlapping spans (including canonical synthetic expansions), `src/Lean/Server/InfoUtils.lean` (blob `a4b04b2b451473b4200b882f9178a833`, `smallestInfo?`, hover, and goal selection) applies explicit range, stop-position, and before/after-tactic rules. In `src/Lean/Elab/Frontend.lean` (blob `fd3760667db96a351b4f654720193c89bbee356e`), `.olean` serialization calls `writeModule` on the final `Environment` without serializing `InfoTree`, while `.ilean` generation calls `Lean.Server.findModuleRefs` on snapshot `InfoTree`s to serialize only a reduced JSON reference/declaration index.

### 5. Pretty-Printing, Delaboration, and Semantic Round-Trip Adequacy

#### Syntax Pretty-Printing (`ppCategory`) vs. Expression Delaboration (`ppExpr`)

- **Syntax pipeline (`src/Lean/PrettyPrinter.lean`)**: `PrettyPrinter.ppCategory` (wrapped by `ppTerm`, `ppTactic`, `ppCommand`) runs `sanitizeSyntax` (`src/Lean/Hygiene.lean`: `sanitizeName` erases macro scopes into fresh inaccessible names when sanitization is enabled) $\rightarrow$ `parenthesizeCategory` (`src/Lean/PrettyPrinter/Parenthesizer.lean`: `parenthesizeCategoryCore`, `categoryParser.parenthesizer`) $\rightarrow$ `formatCategory` (`src/Lean/PrettyPrinter/Formatter.lean`: `unicodeSymbolNoAntiquot.formatter`). Both parsing (`Parser.categoryParserFnImpl` and `Parser.runParserCategory` in `src/Lean/Parser/Extension.lean`) and pretty-printing consult the current extensible `Environment` and `Options`.
- **Expression pipeline (`src/Lean/PrettyPrinter/Delaborator/Basic.lean`, `Options.lean`, `src/Lean/Elab/Notation.lean`)**: `PrettyPrinter.ppExpr` invokes `Delaborator.delab` / `delabCore` (`@[delab]`, `@[app_delab]`) before `ppTerm`. Output varies with `pp.maxSteps`, `pp.all`, `pp.notation`, `pp.parens`, `pp.unicode`, `pp.unicode.fun`, `pp.universes`, `pp.fullNames`, `pp.explicit`, `pp.proofs` (which can replace proof terms with `⋯`), and `preserveForPP` (`expandNotationItemIntoPattern`). Editor suggestions in `src/Lean/Meta/TryThis.lean` (`SuggestionText`, `prettyExtra`, `processEdit`) similarly reflow `TSyntax` using target width, indentation, and column (including a documented indentation `FIXME`).
- **Semantic round-trip criterion (`tests/elab/PPRoundtrip.lean`, `tests/elab/ppUnicode.lean`)**: `checkM` elaborates input syntax to `e`, delaborates and formats with `ppTerm`, reparses via `runParserCategory`, elaborates to `e'`, and checks definitional equality `isDefEq e e'` rather than string or syntax equality. `PPRoundtrip.lean` explicitly documents failing round-trip cases for metavariables and a parser TODO for universe metavariables.

### 6. Multi-Version Stability (`v4.29.0`, `v4.30.0-rc2`, and `v4.34.1`)

Source revalidation across `v4.29.0`, `v4.30.0-rc2`, and `v4.34.1` confirms that the core resolver, macro-hygiene, source-position, `InfoTree`, and pretty-printer architecture is preserved across all three versions:
- `src/Lean/ResolveName.lean` in `v4.34.1` (701 lines, SHA-256 `29568f90bc8c5b71...`) retains `resolveGlobalName` (line 194) with enclosing-namespace-first lookup (`resolveUsingNamespace`), `_root_` stripping in `resolveExact`, `resolveOpenDecls`, `getAliases`, and `filterFieldList` projection splitting.
- `src/Lean/Hygiene.lean` in `v4.34.1` (116 lines, SHA-256 `1f4304254fb225c4...`) retains `Unhygienic`, `eraseMacroScopes` (line 95), and `sanitizeSyntax` / `sanitizeName`.
- `src/Lean/Server/Snapshots.lean` (line 44 `Snapshot.infoTree`) and `src/Lean/Widget/InteractiveGoal.lean` (line 54 `InteractiveGoal`) in `v4.34.1` preserve snapshot-attached `InfoTree` goal recovery.

## Boundaries

- **No fresh Lean CLI or LSP execution in this package**: All findings in this package are derived from pinned `leanprover/lean4` source and checked-in regression tests (`tests/elab/PPRoundtrip.lean`, `tests/elab/ppUnicode.lean`); runtime LSP tactic-state and diagnostic probes are covered in the companion server packages.
- **Not examined**: Parser lexical details (Unicode identifier character tables, string escaping), module-system `import all` private-name encodings, exhaustive catalogs of every `CustomInfo` dynamic payload across Lean/Mathlib/Aeneas, and exhaustive tactic/command round-trip test suites beyond `PPRoundtrip.lean`.
- **Known not to apply**:
  - `SourceInfo.canonical = true` does not mean a token literally exists at that byte range in the source file; it marks generated syntax as eligible for `canonicalOnly := true` hover/diagnostic queries.
  - `.olean` files do not serialize `InfoTree`, and `.ilean` files store only a reduced reference/declaration index rather than local contexts or tactic states.
  - Default `ppExpr` / `ppCategory` output is not byte-stable across options or environments and is not guaranteed to round-trip open metavariables or universe metavariables.
  - Lean `SourceInfo` spans are coordinates in the generated Lean document, not a Rust-to-Lean source map.

## Evidence

### Pinned Source and Test Artifacts (`leanprover/lean4` at `v4.30.0-rc2` `3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` and `v4.34.1` `5045d0056413266e57c625dcd7c365b10e377c52`)

- **Namespace and Name Resolution**:
  - `src/Lean/ResolveName.lean` (`v4.30.0-rc2` blob `9b3d11ee12bdc1ff3885d6da83cb89e7f3130e0c`, lines 382–405, 459–568; `v4.34.1` 701 lines, SHA-256 `29568f90bc8c5b71...`, `resolveGlobalName` at line 194).
  - `src/Lean/Elab/Open.lean` (blob `b91c0aca54d99bcda8fb15df81b71347dafc173c`).
  - `src/Lean/Parser/Command.lean` (blob `9b8d6b4eb39a611ffd3b9db0f9d17b1e7f653f70`).
  - `src/Lean/Elab/BuiltinCommand.lean` (blob `c1f80b79afe80c1cfd08f830b9f6d1014c815b1b`).
  - `src/Lean/Elab/Command/Scope.lean` (blob `95898f00d61b57e79060784cfb5e8ed880754299`).
  - `src/Lean/Elab/Command.lean` (blob `1b9bd263858518f56403e3657821edd56fde2f39`).
  - `src/Lean/Elab/DeclModifiers.lean` (blob `5289bd4dccfec6366e9f03a8db2d483ed8941542`).
  - `src/Lean/Elab/App.lean` (blob `3ecd61a814bff650fe60e0b8f7655f25d7eb05be`).
- **Macro Hygiene**:
  - `src/Init/Prelude.lean` (blob `e55fd8785ca9d4f4b7ea61ce5c6939628d4bfe4b`, lines 5525–5882).
  - `src/Lean/Elab/Quotation/Util.lean` (blob `379e6e6a2d3cd1ddf02db0e3dc98b56534cff7a0`, lines 13–17).
  - `src/Lean/Elab/Quotation.lean` (blob `8213946421eefb8d9285f496a3c5b4e57958e223`, lines 125–153, 243–255).
  - `src/Lean/CoreM.lean` (blob `3403cbfde65a41ea67336b83007ff4d4b5b8f3ca`, lines 184–190).
  - `src/Lean/Hygiene.lean` (`v4.30.0-rc2` blob `fba62a5b700d9d22fd11e2f8726fe4d85bf5b754`, lines 16–44; `v4.34.1` 116 lines, SHA-256 `1f4304254fb225c4...`, `eraseMacroScopes` at line 95).
  - `src/Lean/Elab/AutoBound.lean` (blob `8a012c47a2412c01bf1f5994ef393a3df17cbbd6`, lines 38–49).
  - Upstream documentation: Lean Reference Manual §23.5.1 ("Hygiene") and Sebastian Ullrich & Leonardo de Moura, *Beyond Notations: Hygienic Macro Expansion for Theorem Proving Languages* (2020, arXiv:2001.10490).
- **Parser and Elaborator Source Positions**:
  - `src/Init/Data/String/PosRaw.lean` (blob `505515150dd2e7242b3de08801aa1e660a22f7d3`).
  - `src/Lean/Syntax.lean` (blob `186ff6f39bc50b00793c7c2884ce7c087d29e1ce`).
  - `src/Lean/Data/Position.lean` (blob `f5eae212ed37f753a495437dc7b0c7f6cfeaa945`).
  - `src/Lean/Parser/Types.lean` (blob `84e5c1fc4dc9dea0506b83d22dfe318f1c692d14`).
  - `src/Lean/Parser/Basic.lean` (blob `5b38ff62d8089cb3cebbbf3a70f1fc01b34d98ce`).
  - `src/Lean/Parser/Module.lean` (blob `024a5c10df494caccca4bb908e7bcc32df2530ca`).
  - `src/Lean/Log.lean` (blob `3d40ada008ff57e9c82568661f3c4ecf928f9280`).
- **`InfoTree` and Artifact Persistence**:
  - `src/Lean/Elab/InfoTree/Types.lean` (blob `fdd5cf8581192220ef44328c757ee3f3daa2e781`).
  - `src/Lean/Elab/InfoTree/Main.lean` (blob `7091272391123485ee731b6eedb528324ef515fe`).
  - `src/Lean/Elab/InfoTree.lean` (blob `2bd30aea830988c19fc51176c45c2498cb96c787`).
  - `src/Lean/Server/InfoUtils.lean` (blob `a4b04b2b451473b4200b882f9178a833`).
  - `src/Lean/Language/Basic.lean` (blob `08f9b688fc869224c316175220403c2aeb5eb415`).
  - `src/Lean/Language/Lean.lean` (blob `124d4739bc910eb30ec35844348c785bf9f6c70a`).
  - `src/Lean/Elab/Frontend.lean` (blob `fd3760667db96a351b4f654720193c89bbee356e`).
  - `src/Lean/Server/README.md` (blob `4bac3026e17b604888324821f5725e0338f802e3`).
  - `src/Lean/Server/Snapshots.lean` (line 44 `Snapshot.infoTree` in `v4.34.1`) and `src/Lean/Widget/InteractiveGoal.lean` (line 54 `InteractiveGoal` in `v4.34.1`).
- **Pretty-Printing and Round-Trip Tests**:
  - `src/Lean/PrettyPrinter.lean`, `src/Lean/PrettyPrinter/Delaborator/Basic.lean`, `src/Lean/PrettyPrinter/Delaborator/Options.lean`, `src/Lean/PrettyPrinter/Parenthesizer.lean`, `src/Lean/PrettyPrinter/Formatter.lean`, `src/Lean/Parser/Extension.lean`, `src/Lean/Elab/Notation.lean`, `src/Lean/Meta/TryThis.lean`, `tests/elab/PPRoundtrip.lean`, and `tests/elab/ppUnicode.lean`.

## Revalidation

To revalidate these findings on a newer Lean 4 toolchain:

1. **Name Resolution and Hygiene Diff**: Diff `src/Lean/ResolveName.lean` (`resolveUsingNamespace`, `resolveExact`, `resolveOpenDecls`, `resolveGlobalName`, `preprocessSyntaxAndResolve`, `resolveLocalName`), `src/Lean/Elab/Open.lean` (`elabOpenDecl`), `src/Lean/Elab/Quotation.lean` (`quoteSyntax`), `src/Init/Prelude.lean` (`MacroScopesView`, `addMacroScope`, `withFreshMacroScope`), and `src/Lean/Hygiene.lean` (`eraseMacroScopes`, `sanitizeSyntax`). Execute a single Lean probe file testing inner-vs-outer namespace shadowing, broad vs. selective `open` on a `protected` declaration, `export` aliasing, `_root_` qualification, and a hygienic quotation expanded under a conflicting local/global binding.
2. **Source Position and `InfoTree` Diff**: Diff `SourceInfo` and `replaceRef`/`withRef` in `src/Init/Prelude.lean`, `String.Pos.Raw` in `src/Init/Data/String/PosRaw.lean`, `FileMap.toPosition` in `src/Lean/Data/Position.lean`, `Parser.Module.mkErrorMessage` in `src/Lean/Parser/Module.lean`, `Lean.logAt` in `src/Lean/Log.lean`, `src/Lean/Elab/InfoTree/{Types,Main}.lean`, `src/Lean/Server/InfoUtils.lean`, and `src/Lean/Elab/Frontend.lean`. Run a small probe with `set_option trace.Elab.info true` over ASCII and multi-byte UTF-8 tokens, canonical vs. non-canonical synthetic syntax, and `.olean`/`.ilean` output to verify that `.olean` omits `InfoTree` while `.ilean` retains only the `findModuleRefs` projection.
3. **Pretty-Printing and Delaboration Diff**: Diff `src/Lean/PrettyPrinter.lean`, `src/Lean/PrettyPrinter/Delaborator/{Basic,Options}.lean`, `src/Lean/PrettyPrinter/{Parenthesizer,Formatter}.lean`, and `tests/elab/{PPRoundtrip,ppUnicode}.lean`, and run `PPRoundtrip.lean` (`checkM`) plus generated-syntax round-trip checks under the target project's exact `Environment` and `Options`.
