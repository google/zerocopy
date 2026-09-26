# Rust source-span provenance after expansion at nightly-2026-05-31

## Summary

At `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, a compiler `Span` carries two kinds of information that must not be conflated: a source location and a hygiene/expansion context. `SpanData` stores byte positions plus a `SyntaxContext`; the syntax context links to expansion data that records macro call sites, definition sites, transparency, macro identity, and nested expansion ancestry. The public procedural-macro API exposes the same separation directly: `resolved_at` changes name-resolution behavior without moving the source location, while `located_at` moves the source location without changing resolution behavior.

This means there is no single universal “origin” for a post-expansion token. A procedural macro can use call-site, mixed-site, or definition-site hygiene, copy an input token’s span, or deliberately combine one span’s location with another span’s resolution context. rustc can still recover expansion ancestry while its `SyntaxContext` and `ExpnData` are available: `source_callsite` recursively follows macro call sites to the root context, and expansion data records both the immediate call site and the macro definition. External-crate expansion data also has a representation in the hygiene tables.

Source-file identity is similarly richer than an on-disk path. rustc distinguishes real files from virtual sources such as macro-expansion text, procedural-macro source code, anonymous input, and inline assembly. A span can therefore identify source that has no ordinary local filesystem path. Even for real files, remapped and local paths are separate concerns.

At the pinned Charon revision, most of that provenance does **not** survive serialization. Charon translates a rustc span to a registered file plus one-based line and zero-based display-column endpoints. It does not serialize the rustc `SyntaxContext`, expansion IDs, `ExpnData`, macro definition identity, or the span’s original byte positions. For ordinary span translation, `generated_from_span` is always absent. When Charon translates MIR `SourceInfo`, it can populate `generated_from_span`, but the implementation obtains that relation by following MIR `inlined_parent_scope`; it is therefore an inlining-origin relation at this revision, not a serialization of rustc’s macro-expansion ancestry.

Consequently, a later consumer that only has Charon LLBC cannot reconstruct a full rustc macro backtrace from Charon span metadata alone. It can retain useful file/line/column attribution, normalized paths, crate names, and sometimes source contents, but any design that requires exact macro provenance must capture or preserve additional rustc-side information before that boundary.

No fresh rustc, procedural-macro, Charon, or LLBC execution was performed. The report is based on exact pinned implementation source and public API documentation embedded in that source.

## Applicability

This report applies to:

- Rust compiler and standard/procedural-macro library source at `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, corresponding to the nightly-2026-05-31 toolchain used by the pinned Charon revision.
- Charon `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`, version 0.1.210.

“Source location” below means the source-map location selected by a span: byte positions in rustc and, after Charon translation, file plus line/display-column coordinates. “Hygiene” means the syntax context that controls how identifiers introduced through expansion resolve. “Expansion ancestry” means rustc’s chain of macro/desugaring expansion data, not merely a source location pointing at a macro invocation.

The report describes what information exists and what the pinned Charon boundary retains. It does not prescribe an Anneal source-mapping architecture and does not infer identical behavior for adjacent rustc or Charon revisions.

## Findings

### A rustc span contains byte positions, hygiene context, and a parent-definition field

`rustc_span::SpanData` contains:

- `lo` and `hi` byte positions;
- a `SyntaxContext`, documented as information about the macro expansion that created the code;
- an optional local-definition parent.

The byte positions are interpreted through rustc’s `SourceMap`; they are not themselves a pathname and line number. The syntax context is separate from those positions.

This representation already rules out a model in which “a span” is just a source range. Two spans can point to the same source characters while carrying different name-resolution behavior.

Basis: **source**.

### Location and name-resolution context are independently movable

The public `proc_macro::Span` API makes the separation explicit.

`Span::resolved_at(other)` creates a span with the same line/column information as the receiver but with symbols resolved as though they were at `other`. `Span::located_at(other)` does the converse: it preserves the receiver’s name-resolution behavior while taking `other`’s location.

This is a strong discriminator for source-correspondence work. A diagnostic location does not by itself tell a consumer where an identifier resolves, and a hygiene context does not uniquely determine where a diagnostic should point.

Basis: public API **documentation** in pinned source.

### Call-site, mixed-site, and definition-site spans describe different hygiene policies

The procedural-macro API exposes three important expansion contexts:

- `Span::call_site()` resolves identifiers as if written at the invocation site and permits surrounding call-site code to refer to introduced names.
- `Span::mixed_site()` implements `macro_rules!`-style mixed hygiene: locals, labels, and `$crate` use definition-site-like resolution while other names use call-site resolution. Its location is the call site.
- `Span::def_site()` resolves at the macro definition site; at the examined revision this API is unstable.

A macro can also propagate spans from its input tokens or use `resolved_at`/`located_at` to combine location and resolution behavior. Generated tokens therefore need not share one provenance convention even within one expansion.

Basis: public API **documentation** in pinned source.

### Syntax contexts retain an expansion chain, not just one macro marker

rustc’s `SyntaxContextData` records the outermost expansion ID, its transparency, a parent syntax context, filtered opaque variants, and `$crate` resolution information. The context therefore forms a chain through nested expansions.

Each `ExpnData` records the expansion kind, the macro call-site span, the definition-site span, the macro definition `DefId` when applicable, edition and module information, and the expansion that contains the macro definition. Its documentation gives the nested example in which one macro expands to a second macro and each generated token can be traced through the corresponding call sites.

The important distinction is that `ExpnData::parent` concerns where the macro definition is itself nested. The invocation backtrace is recovered through the syntax context and the call-site span’s context.

Basis: **source**.

### rustc can walk from generated code back toward source call sites while the hygiene graph exists

`Span::parent_callsite` returns the call-site span of the outermost expansion that produced a span. `Span::source_callsite` recursively follows such call sites until it reaches the root syntax context.

The procedural-macro API also exposes unstable `Span::parent` and `Span::source` operations: the former returns the span in the previous macro expansion from which a token was generated, while the latter asks for the origin source span.

These APIs show that rustc has richer provenance available during compilation than a single flattened file/line pair. They do not imply that every later compiler IR or external tool retains that graph.

Basis: **source** + public API **documentation**.

### External-crate expansion provenance has an in-compiler representation

rustc hygiene state keeps separate maps for local and foreign expansion data and hashes. `ExpnData` can also record a `macro_def_id` whose `DefId` identifies the invoked macro.

Thus macro expansion provenance is not intrinsically limited to macros defined in the current crate. The compiler representation has a place for expansion data originating in external crates.

This finding establishes representation capability, not a guarantee that every metadata configuration preserves every historical detail or that all diagnostics expose the same backtrace.

Basis: **source**.

### Source-file identity includes real and virtual sources

rustc’s `FileName` distinguishes real source files from several virtual/non-file inputs, including configuration strings, anonymous command input, macro expansion text, procedural-macro source code, command-line crate attributes, custom parser input, doctests, and inline assembly.

A source span therefore need not correspond to an ordinary filesystem path. The `proc_macro::Span::source_text` documentation reinforces the boundary: recovering source text is best-effort diagnostic functionality and succeeds only when the span corresponds to real source code.

For generated Rust written to an actual file and then parsed—for example a file included from a build-script output directory—the resulting source may instead have ordinary real-file identity. The relevant discriminator is how rustc obtained the source, not whether a human wrote it.

Basis: **source** + public API **documentation**; generated-file implication is **derived**.

### Charon normalizes real filenames and preserves optional source contents

At the pinned revision, Charon translates rustc real filenames into one of two representable forms:

- a local path, with path-separator normalization and special rewriting for sysroot and Cargo-home prefixes; or
- a virtual/remapped path when rustc has no local path for a real source file.

When it first registers a file, Charon records the normalized filename, the crate name associated with the source file, and rustc’s in-memory source contents when those contents are available.

This gives later consumers useful source identity even for dependency and standard-library files, while deliberately reducing machine-specific path differences.

Basis: Charon **source**.

### Pinned Charon does not represent rustc’s non-real `FileName` variants as ordinary source files

`translate_filename` maps non-`Real` rustc filenames to Charon’s `FileName::NotReal`. `translate_span_data` then treats `NotReal` as unsupported and reaches an `unimplemented!` branch instead of registering the file.

Accordingly, the pinned source does not establish general support for serializing spans whose filename is rustc’s virtual macro-expansion, procedural-macro-source, anonymous, or inline-assembly form.

This is distinct from macro-generated code whose chosen span points into a real call-site or definition-site file; those spans can still translate as real files.

Basis: Charon **source**.

### Charon flattens a rustc span to file and display coordinates

`translate_span_data` asks rustc’s source map for the span filename, registers that file, then converts `span.lo()` and `span.hi()` through `lookup_char_pos`. The serialized Charon `Loc` stores a one-based line number and a zero-based `col_display` column.

The Charon `SpanData` itself contains only:

- a Charon file ID;
- beginning line/column;
- ending line/column.

It does not contain rustc’s `SyntaxContext`, expansion ID, `ExpnData`, `macro_def_id`, raw `BytePos` values, or the `SpanData::parent` definition field.

The column is a display column chosen by rustc’s source map, not the original byte offset. Consumers that need byte-precise round trips, especially around multibyte text or display-width-sensitive characters, need a separate validation or mapping layer.

Basis: Charon **source** + **derived** information-loss comparison.

### Charon’s `generated_from_span` is not a serialized rustc macro backtrace at this revision

Charon’s AST documentation describes `generated_from_span` broadly as the place code actually came from for macro expansion, inlining, or similar generation. The pinned producer is narrower.

For an ordinary `translate_span`, Charon always sets `generated_from_span: None`.

For MIR `SourceInfo`, `translate_span_from_source_info` starts with `source_info.span`, walks the MIR source-scope chain only through `inlined_parent_scope`, selects the top-most inlined parent span, and stores that parent as `data` with the original source-info span as `generated_from_span`.

The implementation does not inspect the span’s `SyntaxContext`, `ExpnData`, `parent_callsite`, or `source_callsite` while constructing this field. At this pinned revision, the populated relation therefore records MIR inlining provenance. A macro-generated `source_info.span` may already use a location chosen by rustc’s expansion machinery, but its macro ancestry is not separately serialized in `generated_from_span`.

Basis: Charon **source**; comparison with the broader AST comment is **derived**.

### Full macro provenance cannot be reconstructed from Charon span metadata alone

Once a span has crossed the pinned Charon boundary, the serialized data contains file identity and display coordinates but not the rustc hygiene graph.

Two rustc spans can therefore collapse to the same Charon coordinates while having different syntax contexts or expansion histories. Conversely, a proc macro can deliberately give generated code the location of one token and the resolution behavior of another, and Charon retains only the location-facing portion needed for its coordinates.

A consumer that needs to answer questions such as “which macro invocation produced this operation?”, “was this token definition-site or call-site hygienic?”, or “which nested expansion introduced this identifier?” cannot derive those answers from Charon `SpanData` alone. Such a consumer must either retain rustc-side provenance before translation or accept a weaker source-correspondence claim.

Basis: **derived** from the rustc and Charon representations above.

### Useful diagnostics remain possible without full expansion ancestry, but their meaning is narrower

Charon’s retained file/line/column information can still support diagnostics that point to a Rust source location, and registered files can carry the source text observed by rustc. For many generated operations the chosen rustc span intentionally points at the user’s macro invocation or at an input token, which can produce a useful location even after the hygiene context is gone.

That does not make the mapping one-to-one. A call-site location can stand for many generated operations; definition-site or input-token spans can point somewhere other than the invocation; compiler desugarings can select their own spans; and Charon inlining can overlay a separate origin relation.

A robust diagnostic layer should therefore distinguish “location Charon retained” from “complete provenance of the operation.”

Basis: **derived**.

## Boundaries

- No fresh rustc, procedural-macro, Charon, LLBC, or diagnostic execution was performed.
- The report establishes the representations and source-defined transformations at exact pinned revisions; it does not empirically inventory every span emitted by every built-in macro, declarative macro, proc macro, desugaring, or compiler transform.
- A proc macro controls the spans it assigns to generated tokens. There is no general rule that all proc-macro output is call-site-, mixed-site-, or definition-site-located.
- The presence of foreign expansion data in rustc’s hygiene tables does not establish that every external-crate provenance detail is exposed through every compiler API or preserved under every metadata setting.
- Charon’s source comments describe `generated_from_span` more broadly than the pinned producer implements. This report follows the producer when characterizing what is actually serialized.
- Charon’s real-file handling does not imply support for all rustc virtual `FileName` variants; the pinned translation path explicitly treats non-real names as unimplemented.
- Display columns are not asserted to be interchangeable with byte offsets. No multibyte or tab-width experiment was run on this surface.
- This report does not establish end-to-end mapping from Charon spans through Aeneas-generated Lean to Lean diagnostics. That separate boundary is covered by the end-to-end source-correspondence report.
- This report does not choose whether Anneal should preserve a rustc expansion graph, emit a sidecar, use call-site-only diagnostics, or adopt another mapping design.

## Evidence

**Rust compiler source:** `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`.

- `compiler/rustc_span/src/lib.rs`, blob `2371bf15756dac74f5488d5d0b069ed6673014a5`: `SpanData`; `Span::source_callsite` and `parent_callsite`; `FileName` real/virtual variants; source-map-facing span representation.
- `compiler/rustc_span/src/hygiene.rs`, blob `1c742052783cd364b2a40227dffc55f408d6a2ac`: `SyntaxContextData`, `Transparency`, `ExpnData`, local/foreign expansion tables, expansion ancestry.
- `library/proc_macro/src/lib.rs`, blob `a01bf38a62dbf600db3bc8a06a51fdcf04cf1e2e`: public `Span::call_site`, `mixed_site`, `def_site`, `parent`, `source`, `resolved_at`, `located_at`, and `source_text` contracts.

**Charon source:** `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`.

- `charon/src/ast/meta.rs`, blob `7a80a92ea1b3f3eaff1758554001e32019473237`: Charon `FileName`, `File`, `Loc`, `SpanData`, and `Span` representation.
- `charon/src/bin/charon-driver/translate/translate_meta.rs`, blob `187a703dff83687f369f1903c6646aabdff259d3`: real-file normalization, file registration, `translate_span_data`, `translate_span_from_source_info`, and ordinary `translate_span`.

No evidence above is fresh **execution**.

## Revalidation

For a later rustc or Charon pin, first diff the narrow implementation seams:

1. rustc `SpanData`, `SyntaxContextData`, and `ExpnData`;
2. the public proc-macro `Span` contracts for call-site, mixed-site, definition-site, `resolved_at`, `located_at`, `parent`, and `source`;
3. rustc `FileName` and source-map location representation;
4. Charon `meta::FileName`, `SpanData`, and `Span`;
5. Charon `translate_filename`, `translate_span_data`, and `translate_span_from_source_info`.

On a capable execution surface, build one small pinned workspace containing:

- nested local `macro_rules!` expansions;
- a `macro_rules!` macro imported from another crate;
- a procedural macro that emits otherwise-identical identifiers with call-site, mixed-site, definition-site, copied-input, `resolved_at`, and `located_at` spans;
- a build script that writes a Rust file consumed with `include!`;
- a compiler desugaring such as a `for` loop or async construct;
- a source line with non-ASCII text and tabs before a mapped token;
- one function that is MIR-inlined into another.

At the rustc boundary, preserve each interesting span’s byte range, filename, syntax-context/expansion chain, call sites, definition site, and macro definition identity. Then run the exact Charon revision and preserve serialized file records and spans.

The comparison should answer, case by case:

- which generated constructs retain a real source file;
- which location rustc assigns;
- which hygiene/expansion facts disappear in Charon;
- whether any non-real filename reaches a successful Charon serialization path;
- how line/display-column coordinates behave for multibyte and tabbed input;
- whether `generated_from_span` changes only for MIR inlining as the pinned source predicts.

This probe validates concrete mappings for that revision. It does not prove that all macro libraries choose the same span policy or that the resulting locations are sufficient for every diagnostic use.
