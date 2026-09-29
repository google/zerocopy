# Exact authored edit ranges versus compiler and generated-source provenance

## Summary

In frozen real tool output, Charon's macro-generated `generated` function had an item span inside the macro definition and no `source_text`; rustfmt moved that span from line 35 to lines 47–49 while preserving the function and its marker. Aeneas' generated Lean source named two Rust functions and printed source locations, but those comments only support lexical candidate links. Neither form identifies an exact editable Rust-hosted Lean range.

A separate controlled projection harness recorded exact UTF-8 byte intervals for two invented Rust doc-comment payloads. It round-tripped 102 authored scalar boundaries, distinguished UTF-16 from scalar positions, rejected a surrogate interior, and refused edits into synthetic or generated text. A two-range authored edit applied atomically; five controls rejected the whole action, including a host-file shift that left projected text byte-identical. These are fixture-level ownership results, not evidence that Anneal implements this projection or edit policy.

## Applicability

The macro specimen is a frozen Rust source and LLBC from `anneal-3730-charon-subject-identity-2026-09-29`; this package includes its own copies. The Aeneas specimen is a frozen source, LLBC, and generated `Funs.lean` from `anneal-3730-cross-tool-provenance-2026-09-29`, also copied here. The original macro LLBC came from pinned Charon 0.1.210 with nightly Rust 2026-05-31. This run formatted a copy using locally installed rustfmt 1.9.0 and re-extracted it with the same Charon binary in direct `charon rustc` mode. Because the original was a Cargo extraction, the comparison is limited to item/source-span behavior, not full LLBC identity or equivalent compilation subjects.

The projection/transaction harness uses an **invented** `/// ` payload convention with a synthetic Lean header and footer. Its source contains CRLF, an emoji, a combining mark, a tab, two authored payload lines, and stripped doc-comment prefixes. It is not historical V1 or proposed V2 Anneal syntax. All operations occur on Python strings converted to UTF-8 byte slices for exact edit authority. There is no live Lean server, editor, MCP bridge, or LSP rename call in this package.

The report gives bounded evidence for [#3731](https://github.com/google/zerocopy/issues/3731) I025/I026/I029/I031 and touches I027/I030/I059/I060. It leaves I028/I032 and substantial parts of every other named item open. In the [#3730](https://github.com/google/zerocopy/issues/3730) crosswalk it informs B01–B03/B05/B10/B11/B13/B14 and K01/K03/K07, with actual execution concentrated in B03/B05/B10/B14 and K03/K07.

## Findings

### Charon item spans are evidence about compiler output, not an edit license

The frozen unformatted LLBC contains one local `subject_identity_probe::generated` function with an item span at source line 35, columns 8–40, inside the `macro_rules!` definition. Its `source_text` and `generated_from_span` fields are null. The macro invocation is later in the source. After rustfmt and direct re-extraction, the same named function was local with a span at lines 47:8–49:9, still inside the macro definition; `source_text` and `generated_from_span` remained null. The ordinary `movable` function's span shifted from line 41 to lines 55–57, and its serialized `source_text` changed to match rustfmt's multiline layout. **Basis: execution** for the formatted extraction; **execution evidence reused** for the frozen original.

The function name and marker remained visible, but the physical span changed and the generated item's span did not point to a user-owned macro invocation or to embedded Lean text. A tool can show this as compiler-derived provenance with an explicit confidence label. Promoting it to a writable Rust proof range would require an independent authored-text map or a compiler-authenticated expansion relation that was not present in these item records. **Basis: derived** from the observed span/source-text fields and formatter movement. The prior Charon identity report documents additional feature and duplicate-marker ambiguities.

### Aeneas comments support navigation candidates, not exact reverse mapping

The frozen `snapshot.llbc` has local Charon items `step` and `select`. Frozen `Funs.lean` contains generated definitions with nearby comments naming `[snapshot_probe::step]` and `[snapshot_probe::select]` and printing source ranges `4:0–6:1` and `8:0–10:1`. The harness found exactly those two name/comment pairs and labeled each edge `lexical name/comment match only`. The generated file's imports, options, comments, and translated definitions have no authored Rust-hosted Lean byte interval in this evidence. **Basis: source artifact inspection** through the replay harness.

Those comments can help explain a generated diagnostic or offer an approximate navigation target. They do not show that a requested rename or code-action edit to `Funs.lean` can be written back to the Rust file. The generated-model URI is therefore read-only in the controlled ownership model. **Basis: derived** from the absence of an authenticated item-to-declaration map and an exact authored byte range. The companion cross-tool report contains actual rustc/Charon/Aeneas/Lean diagnostic specimens; this package does not repeat that tool run.

### Exact coordinate and segment checks can be independent of compiler spans

The invented projector copied two payload lines byte-for-byte after stripping each four-byte `/// ` prefix, then added synthetic header/footer text. It recorded exact source and projected UTF-8 byte intervals for each copied line. For every valid scalar boundary inside those intervals, 102 source↔projected byte translations returned to the starting offset. Across the full projected document, 158 Unicode scalar boundaries converted to and from zero-based UTF-16 line/column positions within the defined inverse domain. Six boundaries had different scalar and UTF-16 numeric columns; a position inside the emoji's surrogate pair and a byte inside its UTF-8 sequence were rejected. The CRLF interior was intentionally excluded from the inverse domain. **Basis: execution** of the preserved harness.

This tests one exact-copy transformation. It does not prove a proposed Anneal parser's handling of escaping, indentation normalization, display-width columns, malformed UTF-8, or external editor position-encoding negotiation. The existing `anneal-3730-projection-properties-2026-09-29` report has a larger randomized illustrative suite; this package adds direct comparison with frozen compiler/generated-source provenance and an explicit multi-URI transaction boundary.

### Diagnostic attribution and edit authority must be separate

The fixture's synthetic header and copied payload share one projected document, but only the copied payload has an exact authored Rust origin. An atomic action replacing `True.intro` with `trivial` in both authored lines succeeded. Adding one edit into the synthetic header made the whole action fail as `no-exact-single-origin`; an edit spanning the two payload segments failed the same way. Adding an edit to the generated `Funs.lean` URI failed as `read-only-or-external-uri`, and a generated-file rename resource operation failed as `resource-operation-unsupported`. All four rejected controls left the source byte-identical. **Basis: execution** of the illustrative ownership handler.

Prepending an unrelated Rust line changed the host source hash and shifted every authored byte range while leaving the projected Lean text hash unchanged. An action prepared against the earlier host was rejected as `stale-source-or-projection`, rather than using the old range at a plausible new location. This is a concrete B05/I029 case in the fixture: projection content identity alone is insufficient to authorize a source edit. **Basis: execution**. A diagnostic may still use an approximate anchor when exact mapping is absent; that anchor should carry no edit authority. **Basis: derived** from the failed synthetic/generated controls.

## Boundaries

| Issue scope | Evidence here | Remaining work |
| --- | --- | --- |
| I025/I026 | 158 coordinate boundaries, 102 exact copied-segment boundaries, synthetic rejection | Actual Anneal parser/generator, escaped doc attributes, non-copy transforms, other LSP encodings, invalid Unicode. |
| I027 | Two copied segments and separate candidate links from LLBC to generated Lean | One annotation yielding multiple real obligations, many annotations in one real declaration, diagnostic relation and query routing. |
| I028 | One illustrative projector generated its own text | No actual Anneal batch/live sink comparison, import changes, Lean elaboration equality, or shared production generator. |
| I029 | Host shift with unchanged projection rejects stale patch | Real editor WorkspaceEdit transaction, multi-file CAS, concurrent reorder and A→B→A controls. |
| I030 | Synthetic/generated edit and resource-operation rejection | Real Lean completion/code action/snippet/rename payloads, import suggestions, qualified-name fixes, client capabilities. |
| I031 | Real Charon/Aeneas metadata plus synthetic edit-authority controls | Actual diagnostic responsibility for copied proof, scaffold, generated model, external import, absent source, and related information in one integrated system. |
| I032 | None beyond exact-map construction | Incremental edit-stream map equality, timing, complexity, and Lean incremental reuse; the larger illustrative suite is in the prior projection report. |
| I059/I060 | Generated source kept read-only; multi-range fixture action is atomic | Actual hover/navigation/tokens/rename across annotations and files, partial-client behavior, resource operations and source-unavailable targets. |

The formatter run compared a Cargo-produced frozen LLBC with a fresh direct-rustc LLBC; only the explicit named item spans and text are compared. It does not establish that formatting preserves extracted semantics or proof validity. Raw Charon JSON can vary in keyed map order, so raw hashes are acquisition identities, not semantic equivalence evidence. No Anneal annotation parser, production source map, proof server, or LSP/MCP bridge was executed.

## Evidence

- `support/probe.py`, SHA-256 `15aff27d8721aa746401dee31740ac3f048c1a23b985221fc9d30b470e608026`, is the complete replay. It runs rustfmt/Charon, checks real metadata, enumerates coordinates, and applies guarded fixture actions.
- `support/frozen/` contains the original macro Rust/LLBC and snapshot Rust/LLBC/Aeneas Lean artifacts. Their exact SHA-256 values are recorded in `support/raw-results.json`; key frozen LLBC/Lean hashes are also in `REPORT.json`.
- `support/formatted-macro.rs`, SHA-256 `ef566f0a360a64a26891d93bcf5a42224ab576a16a95b56a8c4a5720bd4b15e5`, and `support/formatted-macro.llbc`, acquired SHA-256 `f538c18d46b1975e626f6d5cad56dc05ab1613653e948753ac5670c2a9a043b1`, preserve the formatter control. rustfmt 1.9.0 binary SHA-256 was `ee717a093f2b2e2c124cde782b4b955fb26ec0c7cf241e6403fed99d624f0c76`.
- `support/raw-results.json`, acquired SHA-256 `47338ec5e3a69cdbfd8a76834f457228be4329c64f6ef820fe8d183b16a20aca`, records all source/projection text, segment maps, coordinate counts, six action outcomes, Charon spans/attributes, Aeneas comment matches, command, exits, and binary/artifact hashes. A prior replay produced the same semantic assertions but different raw Charon and raw-results hashes; keyed serialization order should be inspected rather than treated as behavior.

## Revalidation

Run `python3 support/probe.py` from this package with the identified local Charon/Rust and rustfmt executables, or update those paths while recording new hashes. Compare `generated` and `movable` item spans, `source_text`/`generated_from_span`, exact copied byte intervals, invalid coordinate rejection, and whole-action rejection outcomes. For an Anneal implementation, replace the invented projector/handler with the actual parser, batch/live generator, diagnostic mapper, and editor or MCP transaction API; exercise real generated-model navigation, multi-file rename, and formatter changes with outstanding requests before granting any edit authority beyond exact authored text.
