# Macro and doc-comment projection: ownership, patches, diagnostics, and edit stream

## Summary

A real Rust fixture compiled with pinned nightly rustc and extracted with pinned Charon. Its ordinary function records had physical source spans and `source_text`; the macro-generated function had a span inside the macro definition and no `source_text` or `generated_from_span`. A separate, explicitly **illustrative** projector copied three Rust doc-comment blocks into Lean text: one block fed two obligations, and two blocks fed one declaration. Pinned Lean accepted the baseline text and emitted real diagnostics for copied, scaffold, generated-model, and absent-import specimens.

The model patch handler applied one two-range authored edit atomically, the patched Lean file passed a fresh batch check, and nine controls were rejected, including host-only shift, A→B→A revision, mixed generations, conflicting edits to duplicate projections, synthetic range, generated-model URI, snippet, and resource rename. An 80-step measured stream compared a narrow duplicate-aware indexed update with full regeneration after every step; text and all eight exact maps matched. On this tiny fixture, the indexed path was **slower** in median time (9.625 µs versus 8.2705 µs), so the run does not establish a performance reason to implement it.

This is bounded evidence for [#3731](https://github.com/google/zerocopy/issues/3731) I025–I032 and the [#3730](https://github.com/google/zerocopy/issues/3730) K01/K03/K04/K06/K07 crosswalk. The doc marker `///| `, projection rules, identity guard, and patch handler are test devices, not Anneal syntax or implementation.

## Applicability and provenance boundaries

The fixture is `support/fixture.rs` (SHA-256 `8000c44b932d72c22a026333f3f484d70cd88d33d738e729bedebff9e16c1dc5`), compiled with nightly-2026-05-31 Rust (`rustc` binary SHA-256 `2ab7af1ea2ec5c69195fd8dfb0e1f91afdb7cc1e53127bba416616ce43a18dbc`) and extracted through Charon 0.1.210 (`51bb6d23beab3f97a684c25162d3e402fc820c891b57b21d2ca781c1da211a8b`). The acquired `fixture.llbc` SHA-256 is `a3695b9ecea33c962f1409db4d598fa56d1dce5cedc080fdd7811aff0bc444a7`. The Lean binary is v4.30.0-rc2, SHA-256 `b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997`. Execution was on macOS 26.6.2 arm64 with Python 3.14.7.

Charon placed `annotated`, `first`, and `second` at physical lines 6, 11, and 16 with source text. `macro_generated` had a span beginning at line 20, column 8, inside `macro_rules!`; both `source_text` and `generated_from_span` were null. Thus this real compiler specimen offers a useful provenance warning, not an editable Lean proof range inside the macro invocation. The projector derives exact byte ranges independently from the Rust source's `///| ` payload lines. Rustfmt changed the host Rust bytes (`support/formatted-fixture.rs`, SHA-256 `e2c8ae147c8d1a093cf8d6231a83ce9d7577205bd7f25bc0ba2cf742d4604553`) while its projected Lean text stayed byte-identical. Source identity and positions must therefore remain separate from projection-content identity.

The illustrative generator emits `support/generated.lean` (SHA-256 `88f95120e60ba65cdb9cfa3e9b4ad6e5ee8d07d82d918b437608a3896d1e8181`). Its eight map entries are exact UTF-8 byte copies of the six authored lines, with the first two appearing twice. Synthetic theorem names, types, separators, and imports have no writable Rust range. An attribution anchor for those bytes would not grant edit authority. The harness does not parse historical Anneal annotations, maintain a real LSP document, or attach Charon item IDs to generated declarations.

## One-to-many and many-to-one consequences

The first doc block's `by` and `trivial` lines appear in both `left` and `right`. An edit to one generated occurrence can be applied to the single source range and then regenerated into both; two edits proposing different replacements to those occurrences must conflict. The `conflicting-duplicate` control did reject the whole action. The `combined` theorem assembles two distinct doc blocks; a diagnostic or cursor in it can name one exact copied block when located inside it, but the declaration as a whole has multiple source owners. The `cross-generated-gap` control rejected one edit spanning copied and synthetic bytes. These are model consequences, not observed Anneal query routing.

The successful patch replaced `trivial` with `simp` in the first block and in one range of the combined declaration. It generated both `left` and `right` with `simp`; the resulting three-obligation Lean file passed `lean --json`. All edits passed generation, source-hash, projection-hash, byte, URI, and ownership guards before any source byte was changed. Nine controls returned explicit reasons and left the original source untouched:

| Control | Rejection |
| --- | --- |
| Host-only prefix, unchanged projection; A→B→A source bytes at a newer revision | `stale-generation` in both cases |
| One edit tagged with a different revision | `mixed-generation` |
| Distinct replacements to two projected copies of one source range | `conflicting-duplicate-origin` |
| Synthetic header or a range crossing generated segments | `no-exact-single-origin` in both cases |
| Generated model URI | `read-only-or-external-uri` |
| Snippet placeholder; resource rename | `snippet-unsupported`; `resource-operation-unsupported` |

Deleting one owning doc line violated this strict fixture's three-block/two-line shape and was rejected by projection construction. This is an intentionally narrow parser-failure specimen, not evidence that Anneal recovers correctly from partial syntax. A multi-file editor transaction, partial client capabilities, concurrent agents, and source unavailable after a query remain untested.

## Real Lean diagnostics and responsibility

The baseline generated Lean file exited 0. Replacing an authored `trivial` with `missingProof` yielded four Lean JSON errors, including `unknown tactic` at projected lines 4 and 7: the same authored typo appears in two obligations. The harness preserved each original Lean position and mapped each to the copied doc block as an **exact authored candidate**. Lean's message did not echo the misspelled token; a diagnostic mapper must retain the original location and source range rather than infer ownership from message text.

Changing a synthetic theorem type yielded two errors. One was located in copied proof text and mechanically mapped to an authored byte; another was located on the synthetic declaration and had no exact Rust range. The root cause was the synthetic type change. This counterexample shows why location mapping alone cannot decide responsibility or authorize an edit. Separate actual Lean files produced a generated-model error and a missing external import error; the model classifies those URIs as read-only or external. The original JSON records are preserved, but no production diagnostic routing or related-information protocol was exercised.

## Measured update stream

With seed 3730, the harness alternated 80 edits between `trivial` and `simp` inside two authored blocks. Each source edit changed every generated copy of that source range. After each narrow indexed update, a complete scan/regeneration produced byte-identical Lean text and identical eight-entry maps; all 80 comparisons passed. Total measured indexed time was about 0.81 ms; full regeneration about 0.70 ms for the preserved run. The times are process-local Python measurements of a 511-byte fixture, without warmup, noise model, editor/server cost, or asymptotic scaling. The narrow path handles only one within-line replacement and falls outside its domain for marker, newline, macro, formatting, or block-structure edits. The previously persisted randomized projection-properties report covers broader synthetic Unicode/edit cases; this report adds doc comments, duplicate origins, real compiler/Lean specimens, and patch conflicts.

## Exact residuals

| Scope | Added evidence | Remaining work |
| --- | --- | --- |
| I025/I026; K01 | Eight exact copied byte maps and synthetic boundaries in a doc-comment model; prior Unicode property report remains applicable. | Production annotation parser, escapes/indentation normalization, negotiated editor coordinates, zero-width border policy, actual pre-compiler sidecar. |
| I027; K03 | One authored block used twice, two blocks assembled into one theorem, conflict on duplicate-origin edits; Charon macro span lacks edit evidence. | Real Anneal obligation generator, cursor/context routing, macro expansion provenance, many-to-one proof edit semantics. |
| I028 | One model generator's text passed real Lean batch. | Production batch and live sinks, imported context, incomplete proof, source-map and elaborated-declaration equality. |
| I029; K06 | Version/hash CAS, mixed-generation and owner-deletion controls. | Real editor transaction, concurrent multi-file revisions, query-in-flight deletion and retry behavior. |
| I030 | Snippet/resource/URI/cross-region rejection. | Real Lean completion, code action, qualified-name fix, import suggestion, client capability variations. |
| I031; K04 | Real Lean JSON copied/scaffold/model/import errors and a synthetic-cause/copied-location counterexample. | Integrated responsibility and related-information policy, external source links, diagnostic lifecycle. |
| I032; K07 | 80 duplicate-aware updates equal full regeneration, with measured timings; rustfmt changes host bytes but not projection text. | Boundary fuzzing on actual parser, many-file edit streams, end-to-end latency, production incremental algorithm or decision to use full regeneration. |

## Replay and package validation

Run `python3 support/probe.py` in this package on the documented host with the pinned Rust, Charon, Lean, and rustfmt paths encoded near the top of the script. It recreates the LLBC, Rust metadata, formatted source, Lean specimens, and `support/raw-results.json`, asserting compilation, baseline and patched Lean acceptance, diagnostic classes, patch failures, and full-map equality after every update. Acquired raw LLBC serialization and microsecond timings differ across runs; compare the checked semantic fields. The retained `support/raw-results.json` SHA-256 is `8cea3182b0252c7611523eabe4bd79870e4577027955266d246e3e8de6187135`. Script SHA-256 is `9a6f4fd11ae21b7843e88647f3667ba8ab2bdf6b8eca09e0e2d954203fabbb47`.

This report establishes fixture behavior and failure boundaries. It does not claim an Anneal projection implementation, sound Rust-level proof correspondence, or safe edit authority for any real product integration.
