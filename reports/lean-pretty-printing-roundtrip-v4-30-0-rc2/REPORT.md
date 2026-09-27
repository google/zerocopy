# Lean pretty-printing and semantic round trips at v4.30.0-rc2

## Summary

At Lean `v4.30.0-rc2`, pretty-printed text is regenerated source, not a stable serialization of either source text or kernel expressions.

For existing `Syntax`, `Lean.PrettyPrinter.ppCategory` sanitizes syntax according to pretty-printer options, adds parentheses using the parser-derived parenthesizer for the category, then formats the result using the parser-derived formatter. That pipeline deliberately chooses whitespace, token spellings, and sometimes identifier spellings from the current environment and options. It therefore does not preserve source bytes.

For an `Expr`, the distinction is stronger: `ppExpr` first **delaborates** the kernel expression back into surface `Syntax`, then runs the syntax pretty-printer. Delaboration is extensible and option-sensitive and can choose notation, hide arguments or proofs, instantiate metavariables, beta-reduce, or omit subterms. It is a presentation operation, not an inverse of parsing and elaboration.

Lean's own `tests/elab/PPRoundtrip.lean` captures the useful round-trip property for terms: elaborate a term, delaborate and pretty-print the resulting expression, parse the emitted text again, elaborate it again, and require the two expressions to be definitionally equal. The test does **not** compare source text or syntax trees. It also records known non-round-tripping cases around metavariables and universe metavariables.

For Anneal, generated Lean text should therefore be treated as a candidate program that must be parsed and elaborated in the intended pinned environment. Do not use pretty-printed text equality as semantic identity, and do not assume that changing pretty-printer options, formatting width, imported syntax extensions, or Lean versions preserves emitted text.

Basis: source + checked-in tests + derived.

## Applicability

This report covers `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`, the revision identified as Lean `v4.30.0-rc2` in the Anneal toolchain studied here.

The report distinguishes two related operations:

1. pretty-printing an existing `Syntax` value with `ppCategory`, `ppTerm`, `ppTactic`, or `ppCommand`; and
2. pretty-printing a kernel `Expr`, which first passes through the delaborator.

The strongest round-trip evidence inspected is Lean's term-level `PPRoundtrip` regression test. That test establishes the project's intended check for its covered fixtures, not a theorem that every Lean term, tactic, command, macro expansion, parser extension, or metavariable state round-trips.

The parser, delaborator, parenthesizer, and formatter all consult the current Lean environment or options. A round-trip result is therefore scoped to the environment, syntax extensions, namespace/open declarations, pretty-printer options, and formatting choices that participate in that operation. This report does not generalize those details to adjacent Lean releases.

No fresh Lean execution was performed for this report. The execution-like evidence is limited to checked-in regression tests and their expected assertions at the pinned source revision.

## Findings

### `ppCategory` regenerates text from syntax

`Lean.PrettyPrinter.ppCategory` is the central syntax pretty-printing path. At this revision it:

1. reads the current options;
2. runs `sanitizeSyntax`;
3. runs `parenthesizeCategory`; and
4. runs `formatCategory`.

`ppTerm`, `ppTactic`, and `ppCommand` are category-specific wrappers around that machinery.

This sequence matters because none of those stages promises source-byte preservation. The parenthesizer reconstructs the parentheses needed for the current parser category, while the formatter reconstructs whitespace and layout. The formatter's own module documentation says that it turns a `Syntax` tree into a `Format` while inserting both mandatory whitespace and optional "pretty" whitespace.

The output is thus best understood as a newly rendered textual representation of syntax.

Basis: source.

### The parser and pretty-printer share the current extensible environment

The parser category used to re-read printed text is not a fixed grammar embedded in a serializer. `Parser.categoryParserFnImpl` looks up the category in the parser extension stored in the current `Environment`, then runs its Pratt parser. `Parser.runParserCategory` accepts an explicit environment, parses the requested category, rejects parser errors, and requires the input to be consumed completely.

The pretty-printer is similarly extension-driven. The parenthesizer and formatter select handlers associated with the syntax node kind and parser descriptions in the current environment. Custom syntax can therefore affect both what parses and how a syntax tree prints.

A useful round-trip check must use an environment containing the syntax and pretty-printer extensions expected by the generated text. Printing under one environment and parsing under another is not covered by Lean's own round-trip test pattern.

Basis: source + derived.

### Pretty-printing intentionally normalizes spelling and layout

Several mechanisms make textual identity unsuitable as a correctness criterion.

First, `sanitizeSyntax` may rewrite identifiers containing macro scopes when name sanitization is enabled. `sanitizeName` erases macro scopes and replaces the user-facing name with a fresh inaccessible name. This improves readable output but cannot preserve the original identifier representation.

Second, formatting depends on layout options. The formatter produces a `Format`, and callers eventually choose a width and indentation when rendering it to a string. Lean's `TryThis` code, for example, uses `Format.prettyExtra` with an input width plus the replacement's indentation and column.

Third, token spelling can change. The Unicode-symbol formatter accepts either the Unicode or ASCII token and selects the emitted form using `pp.unicode` and the parser descriptor's `preserveForPP` setting. The checked-in `ppUnicode.lean` tests demonstrate both directions: the same parsed meaning can print with Unicode or ASCII forms depending on options, and some syntax accepted in one spelling prints in a different default spelling. The `fun ... ↦ ...` syntax, for example, is accepted but normally prints with `=>`; a separate option can make the pretty-printer emit `↦`.

`preserveForPP` is a local spelling-control mechanism, not a general source-preservation mode. The notation elaborator deliberately chooses an ASCII pattern for `unicode(..., preserveForPP)` so ordinary delaboration prefers that representation unless a delaborator explicitly produces the Unicode form.

Basis: source + checked-in tests.

### Parenthesization aims at grammatical output, but it is category-specific

`parenthesizeCategory` adds parentheses according to the category's generated or registered parenthesizer. This is the mechanism that lets a syntax tree be rendered with precedence-sensitive parentheses rather than simply concatenating tokens.

The fallback behavior also exposes a limit: when the parenthesizer does not know enough about a category/node relationship, the generic fallback cannot infer arbitrary parentheses. The source explicitly notes a fallback case where a node is never parenthesized because the required parenthesis form is unknown.

This supports a practical claim—use the correct syntax category and current parser environment when generating text—but it does not establish a universal parse-after-print theorem for arbitrary `Syntax`.

Basis: source + derived.

### `Expr` pretty-printing adds a lossy delaboration boundary

`ppExpr` does not print the kernel expression directly as Lean source. It calls `ppUsing e delab`, so the default delaborator first reconstructs surface `Syntax`, then `ppTerm` formats that syntax.

The delaborator is extensible through the `@[delab]`/`@[app_delab]` mechanism. It chooses registered handlers based on expression shape and head constants. Its behavior is also controlled by many pretty-printer options.

Examples at this revision include:

- `pp.explicit` controls implicit arguments;
- `pp.universes` controls universe display;
- `pp.fullNames` controls qualification;
- `pp.notation` controls use of notation;
- `pp.proofs` may replace proof subexpressions with `⋯`;
- `pp.maxSteps` can cause omitted subterms;
- `delabCore` may instantiate metavariables and beta-reduce before delaboration, depending on options.

These choices are appropriate for human-facing presentation. They also mean that delaborated syntax is not a record of the expression's original source and is not necessarily complete enough for re-elaboration under every state/options combination.

Basis: source.

### Lean's checked-in round-trip criterion is semantic, not textual

`tests/elab/PPRoundtrip.lean` defines `checkM` with the following sequence:

1. elaborate and synthesize the input syntax to an expression `e`;
2. delaborate `e`;
3. pretty-print the resulting syntax with `ppTerm`;
4. render the format to a string;
5. parse that string as the `term` category using the current environment;
6. elaborate and synthesize the parsed syntax to `e'`; and
7. require `isDefEq e e'`.

The final criterion is **definitional equality between elaborated expressions**. There is no comparison between the original and printed strings, nor between the original and reparsed syntax trees.

The test also documents limits. A metavariable example is commented as failing to round-trip. A nearby TODO says universe-metavariable syntax needs parser support for a faithful round trip and explicitly rejects merely printing those values as `_` as an adequate presentation for errors and traces.

The checked-in test suite contains many positive fixtures and option variations, but its structure is still regression testing rather than a universal guarantee. The useful reusable lesson is the validation pattern: if generated text is meant to stand for an existing elaborated term, parse and elaborate it and compare the resulting semantics.

Basis: checked-in tests + derived.

### Typed syntax is the preferred input for generated editor suggestions, but Lean still reflows it

Lean's own "Try this" machinery makes the same distinction between structured syntax and opaque text.

A `SuggestionText` can contain either a `TSyntax kind` or a raw `String`. Structured syntax is pretty-printed with `ppCategory kind`; a raw string is returned unchanged. When preparing a text edit, Lean chooses the width, indentation, and source column and renders the format into replacement text.

This shows why `TSyntax` is useful for generated edits: the syntax category drives parenthesization and formatting. It does not make the emitted bytes canonical. The same source file contains a `FIXME` describing an indentation case where a generated replacement is formatted incorrectly.

For Anneal-generated proof or annotation edits, structured syntax plus category-aware printing is preferable to hand-building text when the desired construct can be represented as Lean syntax. The resulting text should still be checked by the parser/elaborator before being treated as valid generated source.

Basis: source + derived.

### Stable machine identity must live above the pretty-printed text

The mechanisms above separate three notions that can otherwise be conflated:

- **source-text identity**: exact bytes, whitespace, comments, Unicode choices, and source spelling;
- **syntax identity**: a particular Lean `Syntax` tree, including node shapes and source/hygiene information; and
- **semantic identity**: the elaborated term represented by text/syntax, with Lean's own round-trip test using definitional equality as the comparison.

The pinned pretty-printer does not establish stability for the first two notions. For the term fixtures Lean itself tests, the useful target is the third.

If Anneal needs durable identities for proofs, obligations, generated annotations, caches, or edits, those identities should not be hashes of default pretty-printer output unless the text format and all relevant rendering inputs have themselves been made part of a deliberate Anneal protocol. Pretty-printed Lean can remain a user-facing or generated-source representation while semantic/source identities are tracked separately.

Basis: source + checked-in tests + derived.

## Boundaries

**No fresh execution.** This report did not run Lean, the round-trip test, or a generated Anneal project. Checked-in tests show intended and regression-tested behavior at the pinned revision but are not fresh runtime observations.

**No universal parse-after-print theorem was found or established.** The inspected implementation provides category-aware parenthesizing and formatting, and the term regression test validates many concrete cases. That does not prove every `Syntax` value emitted by every extension will parse back to an equivalent value.

**Term round-trip evidence is stronger than tactic/command evidence.** `ppTactic` and `ppCommand` share `ppCategory`, but this investigation did not identify an analogous exhaustive semantic round-trip test for those categories.

**Comments and original whitespace are not claimed to survive.** The formatter reconstructs whitespace from syntax and parser formatting rules. This report did not attempt to catalog every source-information field retained in `Syntax`.

**Metavariables remain a known edge.** The pinned `PPRoundtrip` test explicitly records a failing metavariable case and a TODO for universe metavariables. Do not infer that default `ppExpr` output for open/metavariable-heavy proof states is always re-elaboratable to the original expression.

**Output stability across option sets is not expected.** Many `pp.*` options deliberately change notation, qualification, implicit arguments, Unicode, proof presentation, or other output details.

**No adjacent-version continuity.** Lean's pretty-printer and parser-extension internals are revision-sensitive. The findings apply to the pinned revision unless separately revalidated.

## Evidence

All source evidence below is from `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (`v4.30.0-rc2`), inspected on 2026-09-26.

- `src/Lean/PrettyPrinter.lean`
  - `PrettyPrinter.ppCategory`
  - `PrettyPrinter.ppTerm`
  - `PrettyPrinter.ppExpr`
  - `PrettyPrinter.ppTactic`
  - `PrettyPrinter.ppCommand`
  - Establishes the sanitize → parenthesize → format pipeline and the extra delaboration step for expressions.
  - Role: **source**.

- `src/Lean/PrettyPrinter/Delaborator/Basic.lean`
  - `delabAttribute`
  - `Delaborator.delab`
  - `delabCore`
  - Establishes extensible delaboration, option-dependent omission, optional metavariable instantiation/beta reduction, and conversion from `Expr` to surface syntax.
  - Role: **source**.

- `src/Lean/PrettyPrinter/Delaborator/Options.lean`
  - `pp.maxSteps`, `pp.all`, `pp.notation`, `pp.parens`, `pp.unicode`, `pp.unicode.fun`, `pp.universes`, `pp.fullNames`, `pp.explicit`, `pp.proofs`, and corresponding getters.
  - Establishes that printed representation is deliberately option-sensitive.
  - Role: **source**.

- `src/Lean/PrettyPrinter/Parenthesizer.lean`
  - `parenthesizeCategoryCore`
  - `categoryParser.parenthesizer`
  - `parenthesizeCategory`
  - Establishes category-aware parenthesization and its generic fallback boundary.
  - Role: **source**.

- `src/Lean/PrettyPrinter/Formatter.lean`
  - module-level formatter description
  - `unicodeSymbolNoAntiquot.formatter`
  - `formatCategory`
  - Establishes reconstructed whitespace/layout and Unicode/ASCII token selection.
  - Role: **source**.

- `src/Lean/Parser/Extension.lean`
  - `categoryParserFnImpl`
  - `runParserCategory`
  - Establishes environment-dependent parser categories and the complete-input parser used by the round-trip test.
  - Role: **source**.

- `src/Lean/Hygiene.lean`
  - `sanitizeName`
  - `sanitizeSyntax`
  - Establishes optional rewriting of macro-scoped identifier names before pretty-printing.
  - Role: **source**.

- `src/Lean/Elab/Notation.lean`
  - `expandNotationItemIntoPattern`
  - Establishes the `preserveForPP` Unicode/ASCII choice used when notation is converted into a delaboration pattern.
  - Role: **source**.

- `src/Lean/Meta/TryThis.lean`
  - `SuggestionText`
  - `SuggestionText.pretty`
  - `SuggestionText.prettyExtra`
  - `Suggestion.processEdit`
  - Establishes Lean's structured-syntax path for generated editor replacements and its width/indent/column-dependent rendering. The source also preserves a formatting `FIXME`.
  - Role: **source**.

- `tests/elab/PPRoundtrip.lean`
  - `checkM`
  - Establishes Lean's checked-in term round-trip validation pattern: elaborate → delaborate → pretty-print → parse → elaborate → `isDefEq`.
  - The file also records a failing metavariable case and a universe-metavariable TODO.
  - Role: **source** as checked-in test logic; no fresh execution was performed.

- `tests/elab/ppUnicode.lean`
  - Establishes expected output changes under `pp.unicode`, `preserveForPP`, and `pp.unicode.fun`, including accepted syntax whose default printed spelling differs from the input spelling.
  - Role: **source** as checked-in test cases; no fresh execution was performed.

The conclusion that pretty-printed text should not serve as semantic identity is **derived** from these source-level transformations and the semantic criterion in `PPRoundtrip.lean`.

## Revalidation

For a newer Lean revision, the cheapest source-level revalidation is:

1. diff `src/Lean/PrettyPrinter.lean` around `ppCategory`, `ppExpr`, and category wrappers;
2. diff `PrettyPrinter/Delaborator/Basic.lean`, `Formatter.lean`, `Parenthesizer.lean`, `Parser/Extension.lean`, and `Hygiene.lean` for changes to the pipeline or extension lookup;
3. inspect changes to relevant `pp.*` options;
4. inspect `tests/elab/PPRoundtrip.lean` and `tests/elab/ppUnicode.lean` for expanded guarantees, regressions, or removed TODOs; and
5. inspect `Meta/TryThis.lean` if generated edit behavior matters.

On a Lean-capable surface, run the pinned/new revision's existing `PPRoundtrip` test first. For Anneal-specific use, add a narrow generated-source probe that:

- constructs the exact `TSyntax` categories Anneal plans to emit;
- prints them under the exact options and formatting width Anneal will use;
- reparses them under the exact generated project's environment;
- elaborates the reparsed result; and
- checks the semantic property Anneal needs, rather than checking byte equality.

Include fixtures for custom syntax/imports, Unicode versus ASCII notation, nested precedence/parentheses, hygiene-generated names, implicit/universe arguments, and any metavariable-bearing proof-state text Anneal intends to turn into source.

If Anneal later requires stable generated bytes for caching or content addressing, define that stability as an Anneal-owned serialization contract with pinned formatting inputs. Do not infer such a contract from Lean's default pretty-printer.