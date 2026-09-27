# Lean parser and elaborator source positions at v4.30.0-rc2

## Summary

At `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (`v4.30.0-rc2`), Lean's parser and elaborator share a source-position model centered on `Syntax` and `SourceInfo`.

Parser positions are `String.Pos.Raw` offsets into the UTF-8 source string. Parsed atoms and identifiers normally carry `SourceInfo.original`, which records their token start/end positions plus leading and trailing source substrings. Ordinary parser-created `Syntax.node` values usually carry `SourceInfo.none`; their effective start and end positions are recovered from positioned descendants.

Metaprograms can instead produce `SourceInfo.synthetic start end canonical`. A synthetic span associates generated syntax with an existing source range. The `canonical` bit controls whether that generated syntax is eligible to stand in for user-written syntax in position-sensitive interactions such as hovers and diagnostics; it does not mean the generated token literally exists in the source file. Syntax may also have no position at all.

The elaborator's message API treats syntax as an *error-reporting reference*, not as an immutable origin record. `withRef` refuses to replace a positioned current reference with positionless syntax. `logAt` likewise falls back from a positionless requested reference to the current reference, then converts the chosen raw byte range through the current `FileMap` into line/column positions. Consequently, a Lean diagnostic range is a deliberate source anchor chosen by parser/elaborator machinery. It need not be a one-to-one record of the internal object that triggered the diagnostic.

This is sufficient for Anneal to use generated Lean source positions as a coherent coordinate system for Lean-side diagnostics and interactive queries. It is not, by itself, a Rust source map. The existing end-to-end source-correspondence report covers that separate Rust ↔ LLBC ↔ Aeneas Lean ↔ Lean-diagnostic boundary.

No fresh Lean execution was performed. The report is based on exact pinned source and the current published reference corpus.

## Applicability

Primary subject:

- repository: `leanprover/lean4`
- revision: `3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`
- release: `v4.30.0-rc2`

This report covers:

- the representation of parser/elaborator source positions inside a Lean document;
- how parser tokens and composite syntax obtain ranges;
- original, synthetic, canonical, and absent source information;
- parser-error ranges;
- elaborator reference selection and diagnostic anchoring; and
- conversion from raw source offsets to Lean `Position`.

It does not re-report macro hygiene, `InfoTree`, the LSP wire coordinate system, or Rust-to-generated-Lean source correspondence. Those are adjacent subjects with separate reference reports.

## Findings

### Raw source positions are UTF-8 byte offsets

The parser tracks its current position as `String.Pos.Raw`. `String.Pos.Raw` exposes `byteIdx`, arithmetic with a `Char` advances by `Char.utf8Size`, arithmetic with a `String` advances by `String.utf8ByteSize`, and byte-distance/order operations are defined in terms of `byteIdx`.

Parser state therefore moves through the input in byte-addressed coordinates. `ParserState.pos` is a `String.Pos.Raw`; token caches and parser errors use the same type.

`FileMap.toPosition` converts a raw offset to Lean's line/column `Position`. It finds the containing line from precomputed newline offsets, then advances through the source string one decoded character at a time to compute the column. The resulting column is therefore not the raw UTF-8 byte offset.

For Anneal, the useful invariant is: preserve raw Lean positions while relating syntax ranges and generated source; convert them through the exact document `FileMap` only when a human-facing line/column position is required.

Basis: **source**.

### Parsed tokens carry original spans; ordinary parser nodes usually do not

`SourceInfo.original` stores:

- leading source substring;
- token start position;
- trailing source substring; and
- token end position.

The parser's token constructors build atoms and identifiers with exactly that representation. For example, `mkNodeToken`, `mkTokenAndFixPos`, and `mkIdResult` construct `SourceInfo.original` from the parser's `startPos`, `stopPos`, and whitespace substrings.

By contrast, `ParserState.mkNode` and `mkTrailingNode` construct ordinary parser nodes with `SourceInfo.none`. This is intentional: the core `SourceInfo` documentation states that parser-produced nodes do not themselves carry source info; parser source info is associated with atoms and identifiers.

Composite syntax still has an effective range. `Syntax.getPos?` asks for the syntax's head info; for a node with `SourceInfo.none`, head lookup descends to the left-most positioned descendant. `Syntax.getTailPos?` analogously walks from the right when the node itself lacks usable source info. `Syntax.getRange?` combines those two results.

Thus a range obtained from a parsed command or term is often a derived envelope over its first and last positioned tokens, not metadata physically stored on the node.

Basis: **source**.

### Synthetic source info is an explicit source anchor, not textual identity

`SourceInfo.synthetic pos endPos canonical` represents syntax produced by Lean or a metaprogram. The pinned source describes synthetic syntax as generated syntax associated with a source span from an original reference.

The `canonical` flag adds a policy distinction. Canonical synthetic syntax is not literally part of the source, but Lean intends it to be treated as if the user wrote it for hovers and error messages. `SourceInfo.getPos?` and `getTailPos?` accept both original and synthetic positions by default; when `canonicalOnly := true`, non-canonical synthetic positions are hidden.

`SourceInfo.fromRef` makes this relation explicit. Given positioned reference syntax, it creates a synthetic span with the same effective start/end. With `canonical := true`, it produces a canonical synthetic span only when the reference itself has positions acceptable under `canonicalOnly`; otherwise it falls back to non-canonical synthetic source info. If no usable reference range exists, it returns `SourceInfo.none`.

A consumer therefore must not interpret `canonical` as "this token text occurs at this range." It means that Lean considers the synthetic token a canonical interaction/reporting representative for that range.

Basis: **source**.

### Positionless syntax is normal and propagates differently from positioned syntax

`SourceInfo.none` is a first-class state, and `Syntax.missing` has no intrinsic source position. Parser recovery deliberately pushes `Syntax.missing` in several failure paths. Ordinary parser nodes can also have no source info even while their children are positioned.

Position queries are therefore optional throughout the API. A source-position consumer must expect `getPos?`, `getTailPos?`, and `getRange?` to return `none`.

This is not merely defensive API design. Parser recovery and generated syntax create real cases in which a syntax object is meaningful but no direct token span exists.

Basis: **source**.

### Parser errors are anchored either to an unexpected token or to the parser cursor

`Parser.Error` stores an optional `unexpectedTk`. Its documentation says that when no unexpected token is available, `ParserState.pos` supplies an empty error range.

`Parser.Module.mkErrorMessage` implements the distinction:

- if `unexpectedTk` has a range, the error starts at the token start and ends at the token end;
- otherwise the parser cursor is used and the range is empty; and
- for an unexpected token, the start can be moved backward over the preceding trailing-whitespace substring so the reported range also covers insertion points where an expected token could repair the parse.

The function then converts the raw start/end offsets with the input `FileMap`.

Parser diagnostics therefore are not uniformly "the exact bytes of the bad token." Some intentionally describe a repair region, and parser-recovery errors may be anchored at a cursor position.

Basis: **source**.

### The elaborator maintains a current reference and preserves a usable span across positionless syntax

Lean's `MonadRef` machinery gives elaboration code a current reference syntax. The helper `withRef` does not blindly install its argument. It calls `replaceRef`, which keeps the previous reference when the new candidate has no position information. The source states the purpose directly: bias error reporting toward a valid span.

This makes reference position a dynamically inherited context. If an elaborator descends into synthetic or positionless structure, a useful surrounding source anchor can remain current.

This is especially important for generated syntax: internal elaboration can act on a syntax object that is not directly positioned while diagnostics still land on a positioned enclosing construct.

Basis: **source**.

### `logAt` performs a second fallback before producing a diagnostic range

`Lean.logAt` takes an explicit `ref`, but it first applies `replaceRef ref (← getRef)`. It then obtains:

- `pos := ref.getPos?.getD 0`;
- `endPos := ref.getTailPos?.getD pos`; and
- line/column positions via the current `FileMap`.

Thus diagnostics use the explicitly requested syntax when it is positioned, otherwise the current elaborator reference, and ultimately position zero if neither supplies a start. A missing end falls back to the chosen start.

`logErrorAt` and `logWarningAt` are thin severity-specific wrappers around this mechanism.

For Anneal, this means a diagnostic's range should be treated as Lean's selected reporting anchor. It can be precise, inherited, synthetic, or degenerate. It should not be treated as proof that the internal elaboration object itself originated exactly from those bytes.

Basis: **source**.

### Raw range identity and human-facing line/column identity are separate layers

Lean preserves `String.Pos.Raw` inside syntax and parser/elaborator state, then uses `FileMap` to compute human-facing `Position` values. This distinction matters for generated or edited documents.

Raw ranges can be compared, intersected, and used as stable offsets only relative to the exact source string from which their `FileMap` and syntax were created. After text changes, offsets must be interpreted against the corresponding document snapshot; carrying a raw position into a different source string is not intrinsically meaningful.

The existing Lean server and `InfoTree` reference reports cover snapshot/query behavior. The source-position model here supplies the coordinate representation those systems consume.

Basis: **source** + **derived**.

### Lean-document source positions do not create a Rust-to-Lean source map

The current reference corpus already establishes that Aeneas emits item-level Rust/Charon provenance into generated Lean comments and that Lean diagnostics are ranges in the generated Lean document. It also establishes that the pinned upstream chain does not provide a general mapping from arbitrary generated-Lean ranges back to Rust byte ranges.

The parser/elaborator model in this report does not change that conclusion. `SourceInfo` relates Lean syntax to a Lean source span or reference span. A synthetic Lean span can explain where Lean wants an interaction or error to appear in the generated Lean document; it does not encode which Rust operation generated that syntax.

For precise Rust diagnostics, Anneal needs a separate correspondence relation when item-level provenance is insufficient.

Basis: current reference **corpus** + **derived**.

## Boundaries

- No fresh Lean parser, elaborator, language-server, or macro execution was performed.
- This report does not characterize every producer of `SourceInfo`; it documents the central representation and the parser/elaborator paths that determine ordinary source ranges and diagnostics.
- It does not claim that all parser diagnostics cover only offending tokens. The parser intentionally expands some ranges over preceding whitespace.
- It does not claim that all synthetic syntax is canonical. Non-canonical synthetic syntax remains position-bearing under ordinary position queries but is excluded by `canonicalOnly := true`.
- It does not equate canonical synthetic syntax with literal source text.
- It does not re-specify macro-scope hygiene. Position anchoring and hygiene scopes are distinct metadata concerns.
- It does not re-specify `InfoTree`; that report covers elaboration information and position-sensitive queries.
- It does not define LSP UTF-16 coordinates. Lean raw syntax positions and Lean `Position` are upstream of the server's LSP conversion.
- It does not provide Rust ↔ generated-Lean mapping semantics; the end-to-end source-correspondence report covers that boundary.
- Raw positions are only meaningful with the exact source string/document snapshot whose bytes they index.

## Evidence

Primary source: `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`.

- `src/Init/Prelude.lean`, blob `e55fd8785ca9d4f4b7ea61ce5c6939628d4bfe4b`: `SourceInfo`, original/synthetic/none semantics, position queries, composite `Syntax` position lookup, `SourceInfo.fromRef`, `replaceRef`, and `withRef`.
- `src/Init/Data/String/PosRaw.lean`, blob `505515150dd2e7242b3de08801aa1e660a22f7d3`: byte-index representation and UTF-8-sized raw-position arithmetic.
- `src/Lean/Syntax.lean`, blob `186ff6f39bc50b00793c7c2884ce7c087d29e1ce`: syntax ranges, range extraction, and synthetic range constructors.
- `src/Lean/Data/Position.lean`, blob `f5eae212ed37f753a495437dc7b0c7f6cfeaa945`: `Position`, `FileMap`, and raw-offset-to-line/column conversion.
- `src/Lean/Parser/Types.lean`, blob `84e5c1fc4dc9dea0506b83d22dfe318f1c692d14`: `ParserState.pos`, parser errors, position-sensitive recovery, and positionless parser nodes.
- `src/Lean/Parser/Basic.lean`, blob `5b38ff62d8089cb3cebbbf3a70f1fc01b34d98ce`: token construction with `SourceInfo.original`.
- `src/Lean/Parser/Module.lean`, blob `024a5c10df494caccca4bb908e7bcc32df2530ca`: parser-error range construction and `FileMap` conversion.
- `src/Lean/Log.lean`, blob `3d40ada008ff57e9c82568661f3c4ecf928f9280`: current-reference position access and `logAt` diagnostic anchoring.

Current reference-corpus evidence:

- `reports/end-to-end-source-correspondence-nightly-2026-06-03-v4-30-0-rc2/REPORT.md`, blob `f6d9139254827972c6b41ae4bcbb8bbeccd20241`: generated-Lean diagnostic coordinates versus Rust source correspondence.

## Revalidation

For a later Lean revision, re-check these source points first:

1. `SourceInfo` in `src/Init/Prelude.lean`: constructors, `canonical` semantics, and `getPos?` / `getTailPos?`.
2. `Syntax.getHeadInfo?`, `Syntax.getPos?`, and `Syntax.getTailPos?`: whether positionless parser nodes still derive ranges from descendants.
3. `ParserState` and parser node/token constructors: the raw position type and where `SourceInfo.original` is attached.
4. `Parser.Module.mkErrorMessage`: token-range versus cursor-range behavior and whitespace expansion.
5. `replaceRef`, `withRef`, and `Lean.logAt`: fallback rules for positionless references.
6. `FileMap.toPosition`: the conversion from raw offsets to line/column positions.

On an execution-capable surface, preserve a small exact-pin probe with:

- ASCII and multi-byte Unicode tokens, recording raw byte offsets and displayed line/column positions;
- a composite parsed term whose parent node has `SourceInfo.none` but whose children are positioned;
- a parser error with an unexpected token and one at end-of-input;
- a macro expansion that produces both canonical and non-canonical synthetic syntax; and
- an elaborator error raised while the immediate syntax is positionless but an enclosing `withRef` reference is positioned.

Record source text, syntax/source-info dumps, diagnostics, and the exact Lean revision. The discriminators are whether raw positions remain byte-based, whether synthetic canonicality still affects canonical-only queries, and whether diagnostic reference fallback still preserves the enclosing positioned anchor.