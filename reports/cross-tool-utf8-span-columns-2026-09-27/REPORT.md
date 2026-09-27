# Multibyte UTF-8 span and column behavior across Anneal's Rust → Charon → Aeneas → Lean toolchain

## Summary

The Anneal-selected toolchain does **not** use one common meaning for a source “column.” At the exact selected revisions, at least four coordinate systems matter:

| Surface | Line base | Column base | Column unit |
| --- | ---: | ---: | --- |
| rustc JSON diagnostics | 1 | 1 | Unicode scalar values (“characters”) |
| Charon serialized `Loc` | 1 | 0 | rustc **display width** |
| Aeneas source locations | 1 | 0 | Charon display width, printed unchanged |
| Lean batch `--json` `Position` | 1 | 0 | Unicode scalar values |
| Lean LSP `Position` | 0 | 0 | UTF-16 code units |

Rustc JSON also carries `byte_start`/`byte_end`; those byte offsets are the appropriate rustc fields for byte slicing. Lean internally carries UTF-8 byte positions (`String.Pos.Raw`) and explicitly converts them to codepoint columns for ordinary Lean positions and to UTF-16 columns for LSP.

The most important pinned-source finding is a Charon unit mismatch. Charon constructs its serialized `Loc.col` from rustc's `Loc.col_display`, which is terminal-oriented display width. Charon later defines `Loc::to_byte` as `line_start_byte + col` and uses that conversion to build source byte ranges for its own rendered diagnostics. That conversion is valid for simple ASCII prefixes but is not valid in general. After a multibyte character, a wide character, a combining mark, or a tab, display width is not a UTF-8 byte count. The selected Charon source can therefore compute a range endpoint that does not identify the intended source byte position. No fresh failing Charon execution was run here, so the exact user-visible behavior of the downstream renderer for every malformed range remains an execution question; the coordinate mismatch itself is established directly by source.

Aeneas does not repair the Charon unit. Its error formatter prints the serialized `Meta.loc.line` and `.col` integers directly. A consumer that maps Rust/LLBC/Aeneas locations into Lean batch or LSP coordinates must therefore carry an explicit unit tag and source text and perform a conversion; copying a numeric column across layers is incorrect even when examples containing only ASCII make it appear to work.

## Applicability

This report concerns the concrete toolchain selected by current Anneal authority:

- Charon `0.1.210`, `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`;
- that Charon checkout pins Rust `nightly-2026-05-31`; the corresponding compiler source examined here is `rust-lang/rust@f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1` (`rustc 1.98.0-nightly`, commit date 2026-05-30);
- Aeneas `nightly-2026.06.03`, `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`;
- Lean `v4.30.0-rc2`, `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`.

The Rust commit identity was cross-checked against the published `nightly-2026-05-31` compiler version while Charon's own `rust-toolchain` provides the dated toolchain selection. The implementation claims below are bound to the full source commits.

“Character” means a Unicode scalar value/code point unless otherwise stated. It is not a grapheme cluster. “Display width” means rustc's `char_width` accumulation for terminal diagnostics: tabs count as four columns, selected control characters as one, and other scalars use `unicode_width`. “UTF-16 column” means a count of UTF-16 code units as required by Lean's LSP implementation.

The report is about coordinate representation and conversion, not the separate question of path normalization, macro-expansion provenance, or end-to-end semantic source mapping. Charon's `generated_from_span` macro/inlining provenance is relevant only insofar as both stored spans use the same Charon `Loc` representation.

No fresh rustc, Charon, Aeneas, or Lean process was executed. The central coordinate-unit findings and the Charon mismatch follow from pinned implementation source. Execution remains useful for preserving concrete regression specimens and observing renderer failure modes.

## Findings

### Rustc distinguishes byte positions, character columns, and display columns

At the selected Rust compiler revision, a source `Loc` contains all three concepts needed to avoid conflating coordinates:

- the incoming source position is a `BytePos`;
- `Loc.col` is a zero-based `CharPos`;
- `Loc.col_display` is a zero-based display column.

`SourceFile::lookup_file_pos` first converts a relative byte position to a `CharPos` by subtracting the extra UTF-8 bytes used by multibyte scalar values. The line-local `CharPos` is therefore a count of Unicode scalar values, not bytes.

`lookup_file_pos_with_col_display` separately computes display width by taking the first `col` scalar values of the source line and summing `char_width`. At this revision `char_width` assigns tab a width of four, assigns selected control points width one, and otherwise uses `unicode_width`.

The distinction is deliberate. Rustc source comments describe `col_display` as a column “when displayed,” and a nearby fallback comment says the display column is for terminal underlines and is not suitable as a byte offset for tools editing Rust code.

Basis: **source** — `rustc_span` at `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`.

### Rustc JSON exposes byte offsets and codepoint columns, not display columns

The selected rustc JSON diagnostic representation stores:

- `byte_start` / `byte_end`;
- one-based `line_start` / `line_end`;
- one-based `column_start` / `column_end`, documented as character offsets.

The implementation obtains `start` and `end` with `lookup_char_pos` and serializes the column fields from `start.col.0 + 1` and `end.col.0 + 1`, not from `col_display`. It separately serializes `byte_start` and `byte_end` from the source file's original relative byte positions.

This makes rustc JSON unusually explicit for cross-tool consumers: use the byte fields for byte slicing, and use the column fields as human/codepoint positions. Neither should be inferred from the other by simple addition when non-ASCII text precedes the span.

Basis: **source + documentation** — pinned `compiler/rustc_errors/src/json.rs` and `src/doc/rustc/src/json.md`.

### Charon serializes rustc display width as its generic `Loc.col`

At the selected Charon revision, `meta::Loc` is only:

```text
line: usize   // 1-based
col:  usize   // 0-based "column offset"
```

There is no stored byte offset, codepoint offset, UTF-16 offset, or coordinate-unit tag.

`TranslateCtx::translate_span_data` starts from a rustc `BytePos`, calls `SourceMap::lookup_char_pos`, and creates the Charon location as:

```text
line = rustc_loc.line
col  = rustc_loc.col_display
```

It does **not** copy rustc's `loc.col`, and it does not retain the original `BytePos`.

Therefore Charon `Loc.col` at this pin is specifically rustc terminal display width despite the generic “column offset” field comment. The representation is lossy with respect to exact source position. Given only `line` and `col`, the original byte/codepoint position cannot always be recovered.

Basis: **source** — pinned `charon/src/ast/meta.rs` and `charon/src/bin/charon-driver/translate/translate_meta.rs`.

### Charon's display-width coordinate is non-injective for some Unicode text

Because rustc display width is not codepoint count, distinct source boundaries can have the same Charon column.

For example, consider the scalar sequence `a` followed by U+0301 COMBINING ACUTE ACCENT. Rustc's display-width calculation gives the base `a` width one and the combining mark width zero under the selected Unicode-width implementation. The boundary after `a` and the boundary after the combining mark therefore have the same display column even though they have different codepoint and byte offsets.

The same representation also deliberately expands a tab to display width four. A source boundary after one tab has Charon column four even though only one UTF-8 byte and one scalar value precede it.

This is not merely a different convention that can always be inverted. Once only the Charon numeric display column is retained, exact reconstruction requires the source line plus a policy for finding a source boundary with that display width, and some display columns can correspond to multiple boundaries.

Basis: **source + derived** — direct consequence of pinned rustc `char_width` and Charon's choice of `col_display`.

### Charon later treats the display column as a byte count in diagnostic rendering

The selected Charon `meta_utils` defines:

```text
Loc::to_byte(source) =
    byte_offset_of_start_of_line(source, line) + col
```

and `SpanData::to_byte_range` applies that conversion to both endpoints.

`charon/src/errors.rs` uses `span.to_byte_range(source)` when constructing `annotate_snippets` ranges for Charon's own rendered source diagnostics. When source contents are unavailable, its fallback instead passes `span.beg.col + 1` as a character-column value.

This produces a concrete unit mismatch on the source-present path: a display width is added to a UTF-8 byte index.

For a line beginning `éx`, the source boundary after `é` is two UTF-8 bytes from the line start. Rustc's codepoint column is one and, under ordinary width rules, its display column is also one. Charon stores one; `to_byte` then returns byte offset one, which lies inside the two-byte UTF-8 encoding of `é`, not at the intended boundary.

For a line beginning `界x`, the boundary after `界` is three UTF-8 bytes from the start while the display width is two. Charon computes byte offset two, again not the intended boundary.

For a line beginning with a tab, the intended byte offset after the tab is one while the stored display column is four.

The source establishes that these computed ranges are wrong as byte coordinates. This report does not claim a specific downstream panic, clipping, or rendering result for every such range because `annotate_snippets` was not executed here.

Basis: **source + derived** — pinned Charon `meta_utils.rs`, `errors.rs`, and rustc display-width semantics.

### Charon's line/column data is sufficient for ASCII-only examples but unsafe as a universal interchange format

When every preceding source scalar is one UTF-8 byte and has display width one, all of the following happen to be numerically equal:

- byte count from line start;
- Unicode-scalar count;
- rustc display width.

That explains why the mismatch is easy to miss in ASCII fixtures.

The equality stops holding for common source text: non-ASCII identifiers/comments/strings, East Asian wide characters, emoji, combining marks, and tabs. Any Anneal source-map code built from Charon spans must therefore treat “works on ASCII fixtures” as insufficient validation.

Basis: **derived** from the pinned coordinate definitions.

### Macro/inlining provenance does not change Charon's coordinate unit

Charon stores a primary `SpanData` plus an optional `generated_from_span` for macro expansion, inlining, and similar provenance. Both are produced through the same `translate_span_data` conversion and therefore use the same one-based-line / zero-based-display-column representation.

The provenance relation is useful, but it does not provide a hidden byte coordinate that repairs the Unicode ambiguity.

Basis: **source** — pinned Charon span translation.

### Aeneas preserves and prints Charon columns without conversion

At the selected Aeneas revision, `Errors.ml` formats a Charon `Meta.loc` by concatenating:

```text
line : col
```

directly. It does not add one to the column and does not convert display width to codepoint, byte, or UTF-16 units.

Thus an Aeneas diagnostic source location inherited from LLBC uses a one-based line and a zero-based Charon/rustc-display column. A textual Aeneas location like `10:7` must not be assumed to use rustc JSON's one-based codepoint-column convention or Lean's codepoint/LSP conventions.

This path is representational rather than corrective: Aeneas carries forward the Charon coordinate decision.

Basis: **source** — `AeneasVerif/aeneas@ac9f1bc...`, `src/Errors.ml`.

### Lean's ordinary `Position.column` counts Unicode scalar values

At Lean `v4.30.0-rc2`, `FileMap` stores newline positions as raw string positions. `FileMap.toPosition` finds the containing line and computes the column by repeatedly advancing a UTF-8 string position with `String.Pos.next`, incrementing the column by one per decoded `Char`.

Consequently a Lean `Position` is:

- line: one-based;
- column: zero-based;
- column unit: Unicode scalar values.

`FileMap.ofPosition` performs the inverse by advancing `pos.column` scalar values from the stored line start.

This is a codepoint coordinate, not a UTF-8 byte count and not terminal display width.

Basis: **source** — pinned `src/Lean/Data/Position.lean`.

### Lean batch JSON serializes ordinary Lean positions

Lean's command-line reporting path calls `Message.toJson` when JSON mode is enabled. `Message`/`SerialMessage` contains `pos : Position` and optional `endPos : Position`, and its JSON derivation serializes those ordinary Lean positions.

The batch JSON position therefore inherits Lean `Position` semantics: one-based line, zero-based Unicode-scalar column.

This differs from rustc JSON in base but not in underlying scalar-count unit:

- rustc JSON: one-based line, **one-based** scalar column;
- Lean batch JSON: one-based line, **zero-based** scalar column.

A consumer may convert between the two numerically only after accounting for the one-column base difference and only when they refer to corresponding source text.

Basis: **source** — pinned `src/Lean/Message.lean`, `src/Lean/Language/Basic.lean`, and `src/Lean/Data/Position.lean`.

### Lean LSP uses UTF-16 code units, not Lean's batch-JSON column

Lean's LSP code states the protocol distinction explicitly. `leanPosToLspPos` converts a Lean codepoint column into a UTF-16 offset for the line, and subtracts one from Lean's one-based line. The reverse path converts the zero-based LSP line plus UTF-16 character offset back to a UTF-8 string position.

A scalar at or below U+FFFF contributes one UTF-16 code unit. A supplementary scalar such as most emoji contributes two.

Therefore the same boundary can have different numeric columns in Lean batch JSON and Lean LSP. For example, after a single U+1F600 GRINNING FACE on a line:

- Lean batch `Position.column` is 1;
- Lean LSP `Position.character` is 2.

This conversion is deliberate and implemented centrally. An Anneal MCP/LSP bridge should use Lean's LSP conversion semantics rather than sending batch-JSON columns directly as LSP character positions.

Basis: **source** — pinned `src/Lean/Data/Lsp/Utf16.lean`.

### Numeric coincidences across layers are not evidence of shared semantics

Several common examples can produce misleading equal numbers:

- After ASCII text, bytes, codepoints, display width, and UTF-16 code units are all equal.
- After a narrow non-ASCII BMP scalar such as `é`, rustc/Lean codepoint count and Charon display width may be equal, while UTF-8 byte count differs.
- After a wide BMP scalar such as `界`, Charon display width is commonly two while rustc/Lean codepoint count and Lean LSP UTF-16 count are one.
- After a supplementary scalar such as many emoji, Charon display width and Lean LSP UTF-16 count may both be two even though they represent unrelated concepts.
- After a combining mark, display width may fail to advance while codepoint, UTF-16, and UTF-8 positions do advance.

A cross-layer source map must therefore carry the coordinate kind, not infer it from values that happen to agree on a fixture.

Basis: **derived** from the exact source definitions above.

### The robust interchange primitive is an exact byte boundary plus source identity/text

For Rust-source locations, rustc's byte positions identify exact UTF-8 boundaries and can be converted to codepoint, display, or UTF-16 columns when the exact source bytes are available. Charon's current serialized `Loc` discards that byte position and retains only display width, so a downstream consumer cannot generally recover the exact byte boundary from LLBC location metadata alone.

For Lean-source locations, Lean already retains `String.Pos.Raw` UTF-8 positions internally and converts them to the required public coordinate system at the boundary.

For future Anneal diagnostics/source correspondence, the safe design principle is therefore:

1. preserve exact source identity and source bytes;
2. preserve a byte-oriented boundary when the producer has one;
3. tag every exported line/column with its unit and base;
4. convert only at the consumer boundary;
5. never use a terminal display column as a string-slicing offset.

This is a **derived** interoperability requirement, not a claim that Anneal has already adopted such a representation.

## Boundaries

**No fresh execution.** The central findings come from exact pinned source. A concrete regression suite should still run rustc/Charon/Aeneas/Lean on multibyte fixtures and preserve emitted artifacts and diagnostics.

**No claim about grapheme-cluster columns.** None of the inspected core coordinates uses user-perceived grapheme clusters as its fundamental unit.

**No complete terminal-rendering specification.** Rustc's `unicode_width`-based display policy can differ from particular terminals. The report needs only the stronger fact that `col_display` is a display-width coordinate and can differ from bytes/codepoints.

**No claim about every Aeneas output channel.** The inspected Aeneas source-error formatter prints Charon locations directly. Other generated comments or optional metadata outputs may choose different representations and should be checked separately when used as source-map inputs.

**No claim that Charon always crashes on malformed byte ranges.** The pinned source computes incorrect byte endpoints for the cases above. The downstream behavior of `annotate_snippets` for each range was not executed.

**No complete macro-expansion mapping result.** Charon's primary/generated-from span relationship is preserved, but macro-expansion provenance is a separate reference subject.

**No path-relocation result.** File-name normalization and path relocation are adjacent concerns, not part of the column-unit analysis.

**Rust nightly commit mapping.** Charon's immutable `rust-toolchain` pins `nightly-2026-05-31`; the examined rustc source commit is the published compiler commit for that nightly. If a future revalidation discovers a different component commit for a specific target, repeat the narrow rustc source checks below. The relevant `rustc_span` behavior is independently visible in Charon's direct API use.

## Evidence

Evidence was acquired or materially revalidated on 2026-09-27.

### Rust compiler

Subject: `rust-lang/rust@f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`, compiler selected by Charon's `nightly-2026-05-31`.

- `compiler/rustc_span/src/lib.rs`, blob `2371bf15756dac74f5488d5d0b069ed6673014a5`
  - `SourceFile::lookup_file_pos`: converts byte positions to `CharPos`;
  - `SourceFile::lookup_file_pos_with_col_display`: separately derives display width from the source line;
  - `char_width`: tab/control/Unicode-width policy;
  - `Loc`: distinguishes `col : CharPos` from `col_display : usize`.
- `compiler/rustc_span/src/source_map.rs`, blob `47c933e245d4942a81f48dc8bcd6b15ba9c39ea7`
  - `SourceMap::lookup_char_pos`: returns both character and display columns.
- `compiler/rustc_errors/src/json.rs`, blob `04ac140f332618d6fa81254e9a16bc27c729eef5`
  - `DiagnosticSpan`: byte offsets plus one-based character columns;
  - `from_span_full`: serializes `start.col`, not `start.col_display`.
- `src/doc/rustc/src/json.md`, blob `7421dd6210806f8e3a9b310f8f72578830309abe`
  - JSON diagnostic column fields documented as one-based character offsets.

The nightly-to-compiler identity was cross-checked against published rustc metadata for the 2026-05-31 nightly; Charon's own toolchain file supplies the selected nightly date.

### Charon

Subject: `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0` (`0.1.210`).

- `rust-toolchain`, blob `4e348edab20d6bd5b195e758afe20f9d8258a3e1`
  - selects `nightly-2026-05-31`.
- `charon/src/ast/meta.rs`, blob `7a80a92ea1b3f3eaff1758554001e32019473237`
  - `Loc { line, col }` representation and span/file metadata.
- `charon/src/bin/charon-driver/translate/translate_meta.rs`, blob `187a703dff83687f369f1903c6646aabdff259d3`
  - `translate_span_data` stores rustc `loc.col_display` in Charon `Loc.col`.
- `charon/src/ast/meta_utils.rs`, blob `795723c998cf03c930d7c88200577786297f79e6`
  - `line_to_start_byte`, `Loc::to_byte`, and `SpanData::to_byte_range`.
- `charon/src/errors.rs`, blob `e4107c6deb5741d523d2220820d1ee0355adb3c0`
  - source-present diagnostics use `span.to_byte_range(source)`;
  - no-source fallback exposes `span.beg.col + 1` as a character-column display value.

### Aeneas

Subject: `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727` (`nightly-2026.06.03`).

- `src/Errors.ml`, blob `c135674b8601786616c6c20ad81ec388bb8cbfea`
  - `loc_to_string` prints `Meta.loc.line` and `Meta.loc.col` directly.

### Lean

Subject: `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (`v4.30.0-rc2`).

- `src/Lean/Data/Position.lean`, blob `f5eae212ed37f753a495437dc7b0c7f6cfeaa945`
  - `FileMap.toPosition` derives one-based lines and zero-based codepoint columns by advancing one decoded `Char` at a time;
  - `FileMap.ofPosition` performs the inverse codepoint traversal.
- `src/Lean/Data/Lsp/Utf16.lean`, blob `a779f34edfaf80f50c389599b5cd3c67ffcc38b0`
  - explicit UTF-16 conversion;
  - Lean-to-LSP conversion makes lines zero-based and columns UTF-16 code units.
- `src/Lean/Message.lean`, blob `a7f76198c582d1d2032bb24d13ad4cb7a272fa57`
  - messages carry `Position` / optional `endPos`;
  - JSON reporting serializes those positions.
- `src/Lean/Language/Basic.lean`, blob `08f9b688fc869224c316175220403c2aeb5eb415`
  - batch JSON mode prints `msg.toJson`.

Evidence roles: **source**, **documentation**, and **derived** synthesis. No fresh **execution** evidence was produced.

## Revalidation

For another Charon/Rust pin, the cheapest decisive check is source-first:

1. read Charon's pinned Rust toolchain identity;
2. inspect `translate_span_data` and record whether it stores rustc `col`, `col_display`, a byte offset, or a new typed position;
3. inspect Charon's serialized `Loc` representation;
4. inspect every byte-range conversion and diagnostic renderer that consumes that `Loc`;
5. in the corresponding rustc source, verify the definitions of `Loc.col`, `Loc.col_display`, and `char_width`.

For another Lean pin:

1. inspect `FileMap.toPosition` / `ofPosition`;
2. inspect Lean-to-LSP conversion in `Lean.Data.Lsp.Utf16`;
3. inspect batch JSON reporting to determine which position type is serialized.

A minimal execution regression suite should place an intentional diagnostic target after each of these prefixes on otherwise identical lines:

- ASCII: `abc`
- narrow multibyte BMP scalar: `é`
- wide BMP scalar: `界`
- supplementary scalar: `😀`
- combining sequence: `a` + U+0301
- tab

For each fixture, preserve:

- source bytes and a hex dump;
- rustc JSON `byte_start`/`byte_end` and character columns;
- serialized Charon LLBC span values;
- Charon's own rendered diagnostic behavior;
- Aeneas textual source location;
- Lean batch JSON position for an analogous generated-file diagnostic;
- Lean LSP diagnostic range for the same Lean position.

The high-value Charon regression assertion is not merely “the diagnostic looks aligned.” Assert that every derived source slice boundary is a valid UTF-8 boundary and corresponds to the intended rustc byte position. That catches the exact display-width-as-byte-offset failure even if a renderer happens to tolerate or visually mask it.

If Charon changes to retain byte positions or codepoint columns, preserve a specimen from both before and after the change because downstream LLBC consumers may need version-sensitive decoding.
